/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Defs.NeverFails
import VCVio.EvalDist.Instances.OptionT
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Output Distribution of Computations

This file defines `HasEvalDist` and related instances for `OracleComp`.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

open scoped OracleSpec.PrimitiveQuery

namespace OracleSpec

variable {ι} {spec : OracleSpec ι}

/-- A per-query distribution on an `OracleSpec`. Each query index `t : ι` is
assigned a `PMF (spec t)` for its responses. This is the abstract data needed
to lift `OracleComp spec` into `PMF`; uniformity is **not** assumed — see
`IsUniformSpec` for the uniform-sampling specialization.

Specs that should opt into uniform sampling are best registered via
`IsUniformSpec`, which extends this class and additionally carries
`Fintype` / `Inhabited` on each range plus a propositional witness that
`toPMF` is the canonical uniform distribution. -/
class IsProbabilitySpec (spec : OracleSpec ι) where
  /-- The distribution of responses to query `t`. -/
  toPMF (t : ι) : PMF (spec t)

/-- An `OracleSpec` whose responses are uniformly sampled from finite, inhabited
ranges. Bundles `spec.Fintype`, `spec.Inhabited`, and `IsProbabilitySpec spec`
together with a `Prop` witness that the per-query distribution agrees with
`PMF.uniformOfFintype`. Use this as the canonical input to lemmas that
mention `Fintype.card (spec.Range _)` or `PMF.uniformOfFintype` in their
statements. -/
class IsUniformSpec (spec : OracleSpec ι) extends IsProbabilitySpec spec where
  /-- Every response set is finite. -/
  fintype : spec.Fintype
  /-- Every response set is inhabited. -/
  inhabited : spec.Inhabited
  /-- The per-query distribution is the uniform distribution on the response set. -/
  toPMF_eq_uniform : ∀ t, toPMF t = PMF.uniformOfFintype (spec.Range t)

attribute [reducible, instance] IsUniformSpec.fintype IsUniformSpec.inhabited

/-- Bridge from `[spec.Fintype] [spec.Inhabited]` to `IsUniformSpec spec`.
Deliberately **not** an instance — `IsUniformSpec` must be opted into per
spec so that uniform-sampling semantics never attach silently to a spec
whose author didn't intend a probabilistic interpretation. Use this
helper when declaring `IsUniformSpec` for a concrete spec. -/
@[reducible] noncomputable def IsUniformSpec.ofFintypeInhabited
    {ι : Type u} (spec : OracleSpec ι)
    [hF : spec.Fintype] [hI : spec.Inhabited] : IsUniformSpec spec where
  toPMF t := PMF.uniformOfFintype (spec.Range t)
  fintype := hF
  inhabited := hI
  toPMF_eq_uniform _ := rfl

noncomputable instance : IsUniformSpec unifSpec := IsUniformSpec.ofFintypeInhabited _
noncomputable instance : IsUniformSpec coinSpec := IsUniformSpec.ofFintypeInhabited _

/-- Propagate `IsUniformSpec` through `+`: each summand's uniformity is
preserved on its branch. `IsProbabilitySpec (spec + spec')` is derived via
the `extends` chain. -/
noncomputable instance instIsUniformSpecAdd {ι ι'} (spec : OracleSpec ι)
    (spec' : OracleSpec ι') [IsUniformSpec spec] [IsUniformSpec spec'] :
    IsUniformSpec (spec + spec') := IsUniformSpec.ofFintypeInhabited _

/-- Successor to the legacy empty marker `OracleSpec.IsProbSpec`. The replacement
`IsUniformSpec` bundles `Fintype`, `Inhabited`, `IsProbabilitySpec`, and a uniformity
witness. -/
@[deprecated IsUniformSpec (since := "2026-05-20")]
alias _root_.OracleSpec.IsProbSpec := IsUniformSpec

end OracleSpec

export OracleSpec (IsProbabilitySpec IsUniformSpec)

namespace OracleComp

variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type w}

section evalDist_main

/-- Embed `OracleComp` into `PMF` by interpreting each query via the per-query
distribution provided by `IsProbabilitySpec`. -/
noncomputable instance instMonadLiftTPMF [IsProbabilitySpec spec] :
    MonadLiftT (OracleComp spec) PMF where
  monadLift mx := simulateQ IsProbabilitySpec.toPMF mx

noncomputable instance instLawfulMonadLiftTPMF [IsProbabilitySpec spec] :
    LawfulMonadLiftT (OracleComp spec) PMF where
  monadLift_pure := simulateQ_pure _
  monadLift_bind := simulateQ_bind _

/-- Direct `MonadLiftT (OracleComp spec) SetM`: the syntactic / operational
support of `mx`, computed by folding queries to `Set.univ`. Independent of any
probability structure on `spec` — works for arbitrary specs without `Fintype`
or `Inhabited`. The bridge to the probability side is `EvalDistCompatible`
below, supplied only when `[IsUniformSpec spec]`.

Note: This is the *only* `MonadLiftT (OracleComp spec) SetM` instance Lean will
find. The generic `MonadLiftT SPMF SetM` is declared as `MonadLiftT` (not
`MonadLift`), so `monadLiftTrans` cannot chain `OracleComp → SPMF → SetM`. -/
instance instMonadLiftTSetM : MonadLiftT (OracleComp spec) SetM where
  monadLift mx := simulateQ (r := SetM) (fun _ => Set.univ) mx

instance instLawfulMonadLiftTSetM : LawfulMonadLiftT (OracleComp spec) SetM where
  monadLift_pure := simulateQ_pure _
  monadLift_bind := simulateQ_bind _

lemma evalDist_eq_simulateQ [IsProbabilitySpec spec] (mx : OracleComp spec α) :
    𝒟[mx] = simulateQ IsProbabilitySpec.toPMF mx := rfl

/-- Abstract distribution of a single lifted query under `IsProbabilitySpec`:
the per-query distribution `toPMF` is pushed forward through the query's
continuation. Uniform-content sibling: `evalDist_liftM`. -/
lemma evalDist_liftM_toPMF [IsProbabilitySpec spec] (q : OracleQuery spec α) :
    𝒟[(liftM q : OracleComp spec α)] =
      (IsProbabilitySpec.toPMF q.input).map q.cont := by
  simp [evalDist_eq_simulateQ, SPMF.liftM_eq_map, PMF.map_comp, PMF.monad_map_eq_map]

/-- `liftM (query t) : OracleComp spec _` evaluates to the per-query distribution
`IsProbabilitySpec.toPMF t`, lifted to `SPMF`. -/
lemma evalDist_query_toPMF [IsProbabilitySpec spec] (t : spec.Domain) :
    𝒟[(query t : OracleComp spec _)] =
      (IsProbabilitySpec.toPMF t : SPMF (spec.Range t)) := by
  rw [evalDist_liftM_toPMF]; simp [PMF.map_id]

@[simp, grind =] lemma support_liftM (q : OracleQuery spec α) :
    support (liftM q : OracleComp spec α) = Set.range q.cont := by
  change SetM.run (simulateQ (r := SetM) (fun _ => Set.univ) (liftM q)) = Set.range q.cont
  rw [simulateQ_query]
  exact Set.image_univ

@[grind =] lemma support_query (t : spec.Domain) :
    support (query t : OracleComp spec _) = Set.univ := by
  rw [support_liftM]; exact Set.range_id

lemma mem_support_liftM_iff (q : OracleQuery spec α) (u : α) :
    u ∈ support (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = u := by
  rw [support_liftM]; exact Set.mem_range

lemma mem_support_query (t : spec.Domain) (u : spec.Range t) :
    u ∈ support (query t : OracleComp spec _) := by
  rw [support_query]; trivial

alias support_liftM_query := support_query

/-- Support-aware bind congruence: if two continuations agree on all elements in the support
    of `mx`, the resulting bind computations are equal. -/
theorem bind_congr_of_forall_mem_support (mx : OracleComp spec α) {f g : α → OracleComp spec β}
    (h : ∀ x ∈ support mx, f x = g x) : mx >>= f = mx >>= g := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [monad_norm]
    exact h a (by simp [support_pure])
  | query_bind q k ih =>
    change (query q : OracleComp spec _) >>= (fun u => k u >>= f) =
      (query q : OracleComp spec _) >>= (fun u => k u >>= g)
    exact bind_congr fun u => ih u (fun x hx =>
      h x ((mem_support_bind_iff _ _ _).mpr ⟨u, by simp, hx⟩))

@[simp, grind .]
lemma support_finite [spec.Fintype] (mx : OracleComp spec α) : (support mx).Finite := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f h => simpa using Set.finite_iUnion h

end evalDist_main

section finSupport

variable [spec.Fintype]

/-- Finite version of support for when oracles have a finite set of possible outputs.
NOTE: we can't use `simulateQ` because `Finset` lacks a `Monad` instance. -/
instance : HasEvalFinset (OracleComp spec) where
  finSupport {α} _ mx := OracleComp.construct
    (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) mx
  coe_finSupport {α} _ mx := by
    induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx h => simp [h]

@[simp, grind =] lemma finSupport_liftM [DecidableEq α] (q : OracleQuery spec α) :
    finSupport (liftM q : OracleComp spec α) = Finset.univ.image q.cont := by grind

lemma finSupport_query [spec.DecidableEq] (t : spec.Domain) :
    finSupport (query t : OracleComp spec _) = Finset.univ := by grind

lemma mem_finSupport_liftM_iff [DecidableEq α] (q : OracleQuery spec α) (x : α) :
    x ∈ finSupport (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = x := by simp

lemma mem_finSupport_query [spec.DecidableEq] (t : spec.Domain) (u : spec.Range t) :
    u ∈ finSupport (query t : OracleComp spec _) := by grind

end finSupport

section evalDist

variable [IsUniformSpec spec]

@[simp low, grind =]
lemma evalDist_liftM (q : OracleQuery spec α) :
    𝒟[(liftM q : OracleComp spec α)] =
      (PMF.uniformOfFintype (spec.Range q.input)).map q.cont := by
  rw [evalDist_liftM_toPMF, IsUniformSpec.toPMF_eq_uniform]

@[simp, grind =]
lemma evalDist_query (t : spec.Domain) :
    𝒟[(query t : OracleComp spec _)] = PMF.uniformOfFintype (spec.Range t) := by
  rw [evalDist_liftM]; simp [PMF.map_id]

@[simp low, grind =]
lemma probOutput_liftM_eq_div (q : OracleQuery spec α) (x : α) :
    Pr[= x | (liftM q : OracleComp spec α)] =
      (∑' u : spec.Range q.input, Pr[= x | (return q.cont u : OracleComp spec α)])
        / Fintype.card (spec.Range q.input) := by
  have : DecidableEq α := Classical.decEq α
  simp [probOutput_def, div_eq_mul_inv]

@[simp, grind =]
lemma probOutput_query (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | (query t : OracleComp spec _)] =
      (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  simp; rfl

@[grind =]
lemma probEvent_liftM_eq_div (q : OracleQuery spec α) (p : α → Prop) :
    Pr[ p | (liftM q : OracleComp spec α)] =
      (∑' u : spec.Range q.input, Pr[ p | (return q.cont u : OracleComp spec α)])
        / Fintype.card (spec.Range q.input) := by
  have : DecidablePred p := Classical.decPred p
  simp only [probEvent_eq_tsum_ite, probOutput_liftM_eq_div, tsum_fintype, div_eq_mul_inv]
  rw [sum_eq_tsum_indicator]
  simp only [Finset.coe_univ, Set.mem_univ, Set.indicator_of_mem]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => by aesop

@[grind =]
lemma probOutput_query_eq_div (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | (query t : OracleComp spec _)] = 1 / Fintype.card (spec.Range t) := by
  simp

@[simp, grind =]
lemma probEvent_query (t : spec.Domain) (p : spec.Range t → Prop) [DecidablePred p] :
    Pr[ p | (query t : OracleComp spec _)] =
      Finset.card {x | p x} / Fintype.card (spec.Range t) := by
  simp [probEvent_liftM_eq_div]; rfl

end evalDist

section supportEvalDist

variable [IsUniformSpec spec] (oa : OracleComp spec α) (x : α)

/-- Bridge: support computed via the direct `MonadLiftT SetM` agrees with `SPMF.support` of the
distribution semantics. This is the field body for the `EvalDistCompatible (OracleComp spec)`
instance below. The equality is uniform-content: it relies on every response having nonzero
probability, which requires `IsUniformSpec`. -/
private lemma support_eq_SPMF_support (oa : OracleComp spec α) :
    support oa = SPMF.support (𝒟[oa]) := by
  induction oa using OracleComp.inductionOn with
  | pure y => ext z; simp [support_pure]
  | query_bind t mx ih =>
      ext z
      rw [support_bind, support_query]
      simp only [Set.mem_univ, true_and, Set.mem_iUnion, exists_prop]
      simp_rw [ih]
      simp only [SPMF.mem_support_iff, ne_eq, SPMF.apply_eq_toPMF_some]
      rw [evalDist_bind, evalDist_query]
      change (∃ i, ¬ (𝒟[mx i]).toPMF (some z) = 0) ↔
        ¬ ((liftM (PMF.uniformOfFintype (spec.Range t)) : SPMF _) >>= fun u =>
            𝒟[mx u]).toPMF (some z) = 0
      rw [SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_apply,
        tsum_option _ ENNReal.summable]
      have hzero : ((liftM (PMF.uniformOfFintype (spec.Range t))
          : SPMF (spec.Range t))).toPMF none = 0 := by
        simp [SPMF.toPMF_liftM]
      rw [hzero, zero_mul, zero_add]
      have hcontU : ∀ u : spec.Range t,
          ((liftM (PMF.uniformOfFintype (spec.Range t)) : SPMF _)).toPMF (some u) ≠ 0 := by
        intro u
        simp [SPMF.toPMF_liftM, PMF.uniformOfFintype, PMF.uniformOfFinset_apply,
          Finset.card_univ]
      constructor
      · intro h habs
        rw [ENNReal.tsum_eq_zero] at habs
        obtain ⟨u, hu⟩ := h
        have := habs u
        rw [mul_eq_zero] at this
        exact this.elim (hcontU u) hu
      · intro h
        by_contra hcontra
        push Not at hcontra
        apply h
        refine ENNReal.tsum_eq_zero.mpr fun u => ?_
        have := hcontra u
        rw [Option.elim_some, this, mul_zero]

/-- `OracleComp spec` admits the bridge between its direct `support` semantics and the
`SPMF.support` of its `evalDist`. -/
instance instEvalDistCompatible : EvalDistCompatible (OracleComp spec) where
  support_eq_SPMF_support oa := support_eq_SPMF_support oa

/-- An output has non-zero probability in `evalDist` iff it is in computation support. -/
@[simp]
lemma mem_support_evalDist_iff :
    some x ∈ (𝒟[oa]).run.support ↔ x ∈ support oa := by
  rw [support_eq_SPMF_support, PMF.mem_support_iff, SPMF.mem_support_iff,
    SPMF.apply_eq_toPMF_some, SPMF.run_eq_toPMF]

alias ⟨mem_support_of_mem_support_evalDist, mem_support_evalDist⟩ := mem_support_evalDist_iff

/-- Finite-support variant of `mem_support_evalDist_iff`. -/
@[simp]
lemma mem_support_evalDist_iff' [DecidableEq α] :
    some x ∈ (𝒟[oa]).run.support ↔ x ∈ finSupport oa := by
  rw [mem_support_evalDist_iff (oa := oa) (x := x), mem_finSupport_iff_mem_support]

alias ⟨mem_finSupport_of_mem_support_evalDist, mem_support_evalDist'⟩ := mem_support_evalDist_iff'

end supportEvalDist

section NeverFail

variable [IsProbabilitySpec spec]

@[simp]
lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : probFailure oa = 0 ↔ NeverFail oa := by
  simp [neverFail_iff]

@[simp]
lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < probFailure oa ↔ ¬ NeverFail oa := by
  simp [neverFail_iff]

lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : probFailure oa = 0) :
    NeverFail oa := by rwa [← probFailure_eq_zero_iff]

lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < probFailure oa) :
    ¬ NeverFail oa := by rwa [← probFailure_pos_iff]

end NeverFail

section evalDistConvenience

variable [IsUniformSpec spec] [IsProbabilitySpec spec']

lemma evalDist_query_bind
    (t : spec.Domain) (ou : spec.Range t → OracleComp spec α) :
    𝒟[(query t : OracleComp spec _) >>= ou] =
      (OptionT.lift (PMF.uniformOfFintype (spec.Range t))) >>= (evalDist ∘ ou) := by
  rw [evalDist_bind, evalDist_query]; rfl

lemma probOutput_congr {x y : α} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : x = y) (h2 : 𝒟[oa] = 𝒟[oa']) : Pr[= x | oa] = Pr[= y | oa'] := by
  simp_rw [probOutput_def, h1, h2]

lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ support oa → (p x ↔ q x))
    (h2 : 𝒟[oa] = 𝒟[oa']) : Pr[ p | oa] = Pr[ q | oa'] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_def, h2]
  congr 1; ext x
  by_cases hx : x ∈ support oa
  · unfold Set.indicator
    split_ifs with hp hq hq
    · rfl
    · exact absurd ((h1 x hx).mp hp) hq
    · exact absurd ((h1 x hx).mpr hq) hp
    · rfl
  · unfold Set.indicator
    have : (𝒟[oa]) x = 0 := by
      by_contra hne
      apply hx
      rw [support_eq_SPMF_support]
      exact (SPMF.mem_support_iff _ _).mpr hne
    rw [h2] at this
    split_ifs <;> simp [this]

lemma evalDist_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, Pr[= x | oa] = Pr[= x | oa']) : (𝒟[oa]).run = (𝒟[oa']).run := by
  have heval : 𝒟[oa] = 𝒟[oa'] := evalDist_ext h
  simp [heval]

lemma probFailure_eq_sub_probEvent' (oa : OracleComp spec α) :
    Pr[⊥ | oa] = 1 - Pr[ fun _ => True | oa] :=
  _root_.probFailure_eq_sub_probEvent oa

end evalDistConvenience

section guard

variable [IsProbabilitySpec spec]

@[simp] lemma probOutput_guard {p : Prop} [Decidable p] :
    Pr[= () | (guard p : OptionT (OracleComp spec) Unit)] = if p then 1 else 0 := by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probOutput_pure_self ()
  · -- `probOutput_failure ()` would suit, but `LawfulFailure (OptionT (OracleComp spec))` does
    -- not resolve through `OptionT.instLawfulFailure` due to a universe-inference quirk in the
    -- post-refactor diamond. Compute directly.
    rw [OptionT.probOutput_eq, OptionT.run_failure]
    rw [show (pure none : OracleComp spec (Option Unit)) = pure none from rfl, probOutput_pure]
    aesop

@[simp] lemma probFailure_guard {p : Prop} [Decidable p] :
    Pr[⊥ | (guard p : OptionT (OracleComp spec) Unit)] = if p then 0 else 1 := by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probFailure_pure ()
  · -- See note above.
    rw [OptionT.probFailure_eq, OptionT.run_failure]
    simp

lemma probOutput_eq_sub_probFailure_of_unit {oa : OracleComp spec PUnit} :
    Pr[= () | oa] = 1 - Pr[⊥ | oa] := by
  have h := tsum_probOutput_add_probFailure oa
  have hunit : ∑' x : PUnit, Pr[= x | oa] = Pr[= () | oa] :=
    tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx)
  rw [hunit] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probFailure_le_one) h

private lemma probOutput_bind_guard_eq_probEvent {α : Type} (oa : OracleComp spec α)
    (p : α → Prop) [DecidablePred p] :
    Pr[= () | (do let a ← oa; guard (p a) : OptionT (OracleComp spec) Unit)] = Pr[ p | oa] := by
  rw [probOutput_bind_eq_tsum]
  simp only [OptionT.probOutput_liftM, probOutput_guard]
  rw [probEvent_eq_tsum_ite]
  congr 1; ext a
  split_ifs <;> simp

lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
    [NeverFail oa] {p : α → Prop} [DecidablePred p] :
    Pr[= () | (do let a ← oa; guard (p a) : OptionT (OracleComp spec) Unit)] =
      1 - Pr[= () | (do let a ← oa; guard (¬ p a) : OptionT (OracleComp spec) Unit)] := by
  rw [probOutput_bind_guard_eq_probEvent, probOutput_bind_guard_eq_probEvent]
  have h := probEvent_compl oa p
  simp only [probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probEvent_le_one) h

end guard

section simulateQ_evalDist

variable [IsProbabilitySpec spec] [IsProbabilitySpec spec']

/-- If an oracle implementation preserves the distribution of each source query, then
`simulateQ` preserves the distribution of every source computation. -/
lemma evalDist_simulateQ_eq_evalDist
    (so : QueryImpl spec' (OracleComp spec))
    (h : ∀ t : spec'.Domain, 𝒟[so t] =
      𝒟[(query t : OracleComp spec' (spec'.Range t))])
    (oa : OracleComp spec' α) :
    𝒟[simulateQ so oa] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t mx ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, evalDist_bind, ih]
      rw [h t]

end simulateQ_evalDist

section supportWhen

/-- The possible outputs of `mx` when queries can output values in the specified sets.
NOTE: currently proofs using this should reduce to `simulateQ`. A full API would be better -/
def supportWhen (o : QueryImpl spec Set) (mx : OracleComp spec α) : Set α :=
  simulateQ (r := SetM) o mx

@[simp]
lemma supportWhen_pure (o : QueryImpl spec Set) (x : α) :
    supportWhen o (pure x : OracleComp spec α) = {x} := by
  simp [supportWhen]

@[simp]
lemma supportWhen_query_bind (o : QueryImpl spec Set) (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    supportWhen o ((query q : OracleComp spec _) >>= oa) =
      ⋃ x ∈ o q, supportWhen o (oa x) := by
  simp only [supportWhen, simulateQ_query_bind]
  exact Set.bind_def

/-- Reachable outputs of a bind are the reachable outputs of the continuation over reachable
outputs of the first computation. -/
@[simp]
lemma supportWhen_bind (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) :
    supportWhen o (oa >>= ob) = ⋃ x ∈ supportWhen o oa, supportWhen o (ob x) := by
  simp only [supportWhen, simulateQ_bind]
  exact Set.bind_def

/-- Membership form of [`OracleComp.supportWhen_bind`]. -/
lemma mem_supportWhen_bind_iff (o : QueryImpl spec Set) (oa : OracleComp spec α)
    (ob : α → OracleComp spec β) (y : β) :
    y ∈ supportWhen o (oa >>= ob) ↔
      ∃ x ∈ supportWhen o oa, y ∈ supportWhen o (ob x) := by
  simp [supportWhen_bind]

/-- Enlarging the set of possible oracle outputs only enlarges the reachable output set. -/
lemma supportWhen_mono {o₁ o₂ : QueryImpl spec Set}
    (h : ∀ q, o₁ q ⊆ o₂ q) (oa : OracleComp spec α) :
    supportWhen o₁ oa ⊆ supportWhen o₂ oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y with
  | pure x =>
      simpa [supportWhen_pure] using hy
  | query_bind q oa ih =>
      simp only [supportWhen_query_bind, Set.mem_iUnion, exists_prop] at hy ⊢
      rcases hy with ⟨u, hu, hy⟩
      exact ⟨u, h q hu, ih u hy⟩

end supportWhen

section evalDistWhen

/-- The output distribution of `mx` when queries follow the specified distribution. -/
@[reducible, simp]
noncomputable def evalDistWhen (d : QueryImpl spec SPMF) (mx : OracleComp spec α) : SPMF α :=
  simulateQ (r := SPMF) d mx

end evalDistWhen

end OracleComp
