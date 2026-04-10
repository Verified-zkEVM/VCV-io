/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.WriterT
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Logging Queries Made by a Computation

-/

universe u v w

open OracleSpec OracleComp

variable {ι} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Given that `so` implements the oracles in `spec` using the monad `m`,
`withLogging so` gives the same implementation in the extension `WriterT (QueryLog spec) m`,
by logging all the queries to the writer monad before forwarding the response. -/
def withLogging (so : QueryImpl spec m) : QueryImpl spec (WriterT (QueryLog spec) m) :=
  fun t : spec.Domain => do let u ← so t; tell [⟨t, u⟩]; return u

@[simp, grind =]
lemma withLogging_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withLogging t = do let u ← so t; tell [⟨t, u⟩]; return u := rfl

lemma fst_map_run_withLogging [LawfulMonad m] (so : QueryImpl spec m) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withLogging) mx).run =
    simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

/-- Logging preserves failure probability: for any base monad `m` with `HasEvalSPMF`,
wrapping an oracle implementation with `withLogging` does not change the probability of failure.
When `m = OracleComp spec`, both sides are `0` (trivially true). When `m` can genuinely fail
(e.g. `OptionT (OracleComp spec)`), this is a non-trivial faithfulness property. -/
lemma probFailure_run_simulateQ_withLogging [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withLogging) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [show Pr[⊥ | (simulateQ (so.withLogging) mx).run] =
    Pr[⊥ | Prod.fst <$> (simulateQ (so.withLogging) mx).run] from
    (probFailure_map _ _).symm, fst_map_run_withLogging]

lemma NeverFail_run_simulateQ_withLogging_iff [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withLogging) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_run_simulateQ_withLogging]

end QueryImpl

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in. -/
def loggingOracle {spec : OracleSpec ι} :
    QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withLogging

namespace loggingOracle


/-- Specialization of `QueryImpl.probFailure_run_simulateQ_withLogging` to `loggingOracle`. -/
@[simp]
lemma probFailure_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) :
    Pr[⊥ | (WriterT.run
        (simulateQ (loggingOracle (spec := spec)) oa) :
          OracleComp spec (α × spec.QueryLog))] = Pr[⊥ | oa] := by
  rw [loggingOracle, QueryImpl.probFailure_run_simulateQ_withLogging, simulateQ_ofLift_eq_self]

@[simp]
lemma fst_map_run_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (loggingOracle (spec := spec)) oa).run = oa := by
  rw [loggingOracle, QueryImpl.fst_map_run_withLogging, simulateQ_ofLift_eq_self]

@[simp]
lemma run_simulateQ_bind_fst {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ (loggingOracle (spec := spec)) oa).run >>= fun x => ob x.1) = oa >>= ob := by
  rw [← bind_map_left Prod.fst, fst_map_run_simulateQ]

/-- Specialization of `QueryImpl.NeverFail_run_simulateQ_withLogging_iff` to `loggingOracle`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {spec : OracleSpec.{0, 0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) :
    NeverFail (simulateQ (loggingOracle (spec := spec)) oa).run ↔ NeverFail oa := by
  rw [loggingOracle, QueryImpl.NeverFail_run_simulateQ_withLogging_iff, simulateQ_ofLift_eq_self]

@[simp]
lemma probEvent_fst_run_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[ fun z => p z.1 | (simulateQ (loggingOracle (spec := spec)) oa).run] = Pr[ p | oa] := by
  rw [show (fun z : α × spec.QueryLog => p z.1) = p ∘ Prod.fst from rfl,
    ← probEvent_map, fst_map_run_simulateQ]

@[simp]
lemma probOutput_fst_map_run_simulateQ {spec : OracleSpec.{0, 0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (loggingOracle (spec := spec)) oa).run] =
      Pr[= x | oa] := by
  rw [fst_map_run_simulateQ]

end loggingOracle

namespace OracleComp

lemma run_simulateQ_loggingOracle_query_bind
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) :
    (simulateQ loggingOracle (liftM (query t) >>= mx)).run =
      (query t : OracleComp spec _) >>= fun u =>
        (fun p : α × QueryLog spec => (p.1, (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: p.2))
          <$> (simulateQ loggingOracle (mx u)).run := by
  simp [loggingOracle, QueryImpl.withLogging, OracleQuery.cont_query,
    Prod.map, Function.id_def]

/-- `loggingOracle` preserves `IsTotalQueryBound`: the query structure of
`(simulateQ loggingOracle oa).run` is identical to that of `oa` (each query passes through
unchanged, with only the writer log being appended). -/
theorem isTotalQueryBound_run_simulateQ_loggingOracle_iff
    {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] {α : Type}
    (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound ((simulateQ loggingOracle oa).run) n ↔
    IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ =>
      constructor <;> intro _ <;> trivial
  | query_bind t mx ih =>
      rw [run_simulateQ_loggingOracle_query_bind]
      rw [isTotalQueryBound_query_bind_iff, isTotalQueryBound_query_bind_iff]
      exact and_congr_right fun _ => forall_congr' fun u =>
        (isQueryBound_map_iff _ _ _ _ _).trans (ih u (n - 1))

/-- A total query bound controls the length of every `loggingOracle` trace in support:
if `oa` makes at most `n` queries, then every support point of
`(simulateQ loggingOracle oa).run` has log length at most `n`. -/
theorem log_length_le_of_mem_support_run_simulateQ
    {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [spec.DecidableEq] [spec.Fintype] [spec.Inhabited] {α : Type}
    {oa : OracleComp spec α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    {z : α × QueryLog spec}
    (hz : z ∈ support ((simulateQ loggingOracle oa).run)) :
    z.2.length ≤ n := by
  suffices h : ∀ (β : Type) (ob : OracleComp spec β) (m : ℕ),
      IsTotalQueryBound ob m → ∀ z ∈ support ((simulateQ loggingOracle ob).run),
      z.2.length ≤ m from
    h α oa n hbound z hz
  intro β ob m hm
  induction ob using OracleComp.inductionOn generalizing m with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure] at hz
      subst hz
      simp
  | query_bind t mx ih =>
      intro z hz
      rw [isTotalQueryBound_query_bind_iff] at hm
      obtain ⟨hpos, hrest⟩ := hm
      simp only [simulateQ_bind, simulateQ_query] at hz
      rw [show ((query t).cont <$> loggingOracle (query t).input >>=
        fun x => simulateQ loggingOracle (mx x) :
        WriterT (QueryLog spec) (OracleComp spec) β).run =
        ((query t).cont <$> loggingOracle (query t).input).run >>=
        fun p => Prod.map id (p.2 ++ ·) <$>
          (simulateQ loggingOracle (mx p.1)).run
        from WriterT.run_bind' _ _] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      have hqu_log : qu.2.length = 1 := by
        simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query] at hqu
        have hrun : (loggingOracle (spec := spec) t).run =
            (query t : OracleComp spec _) >>= fun u =>
              pure (u, [⟨t, u⟩]) := by
          simp [loggingOracle, QueryImpl.withLogging_apply,
            WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
            map_pure, Prod.map]
        rw [hrun] at hqu
        simp only [support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff] at hqu
        obtain ⟨u, _, rfl⟩ := hqu
        simp
      have hz'_len : z'.2.length ≤ m - 1 :=
        ih qu.1 (m - 1) (hrest qu.1) z' hz'
      have hm : 1 + (m - 1) = m := by omega
      simpa [List.length_append, hqu_log, hm] using Nat.add_le_add_left hz'_len 1

end OracleComp

/-- Add a query log to a computation using a logging oracle. -/
@[reducible] def OracleComp.withQueryLog {α} (mx : OracleComp spec α) :
    OracleComp spec (α × QueryLog spec) :=
  WriterT.run (simulateQ (QueryImpl.ofLift spec (OracleComp spec)).withLogging mx)
