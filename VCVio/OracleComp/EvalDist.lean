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

This file defines the `MonadLiftT`-based probability and support semantics for `OracleComp`.
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
    simpa only [monad_norm] using h a (by simp)
  | query_bind q k ih =>
    change (query q : OracleComp spec _) >>= (fun u => k u >>= f) =
      (query q : OracleComp spec _) >>= (fun u => k u >>= g)
    exact bind_congr fun u => ih u fun x hx =>
      h x ((mem_support_bind_iff _ _ _).mpr ⟨u, by simp, hx⟩)

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
  exact tsum_congr fun x => by aesop

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
  | pure y => simp
  | query_bind t mx ih => ext z; simp [ih]

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

/-- Two events have equal probabilities when their predicates agree on the support of the
first computation and the two computations share an evaluation distribution. -/
lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ support oa → (p x ↔ q x))
    (h2 : 𝒟[oa] = 𝒟[oa']) : Pr[ p | oa] = Pr[ q | oa'] := by
  have hpr : (Pr[= · | oa]) = (Pr[= · | oa']) := funext fun x => probOutput_congr rfl h2
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator, hpr]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support oa
  · have hs : x ∈ ({x | p x} : Set α) ↔ x ∈ ({x | q x} : Set α) := h1 x hx
    by_cases hp : x ∈ ({x | p x} : Set α)
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hs.mp hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (hs.not.mp hp)]
  · have hz : Pr[= x | oa'] = 0 := congrFun hpr.symm x ▸ probOutput_eq_zero_of_not_mem_support hx
    rw [Set.indicator_apply_eq_zero.2 fun _ => hz, Set.indicator_apply_eq_zero.2 fun _ => hz]

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
    simp [OptionT.probOutput_eq, OptionT.run_failure, probOutput_pure]

@[simp] lemma probFailure_guard {p : Prop} [Decidable p] :
    Pr[⊥ | (guard p : OptionT (OracleComp spec) Unit)] = if p then 0 else 1 := by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probFailure_pure ()
  · -- See note above.
    simp [OptionT.probFailure_eq, OptionT.run_failure]

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
  simp only [probOutput_bind_eq_tsum, OptionT.probOutput_liftM, probOutput_guard,
    probEvent_eq_tsum_ite]
  exact tsum_congr fun a => by split_ifs <;> simp

lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
    [NeverFail oa] {p : α → Prop} [DecidablePred p] :
    Pr[= () | (do let a ← oa; guard (p a) : OptionT (OracleComp spec) Unit)] =
      1 - Pr[= () | (do let a ← oa; guard (¬ p a) : OptionT (OracleComp spec) Unit)] := by
  simp only [probOutput_bind_guard_eq_probEvent]
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probEvent_le_one)
    (by simpa only [probFailure_of_liftM_PMF, tsub_zero] using probEvent_compl oa p)

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
        OracleQuery.input_query, evalDist_bind, ih, h t]

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

section supportPeel

/-- `obtain`-friendly bind support peeler at the bare `OracleComp` level. Unlike `rw
[mem_support_bind_iff]`, applying this lemma to a hypothesis uses *definitional* unification to
match `mx >>= f`, so it engages through the `Monad`/`MonadLift` instance-tree mismatches that block
the syntactic `rw` (the elaborated `OracleComp.instMonad`/`Bind.bind` spelling produced by
unfolding nested protocol definitions differs syntactically from the canonical `>>=`). -/
lemma mem_support_bind_peel (mx : OracleComp spec α) (f : α → OracleComp spec β) {y : β}
    (hy : y ∈ support (mx >>= f)) :
    ∃ a, a ∈ support mx ∧ y ∈ support (f a) := by
  rwa [mem_support_bind_iff] at hy

/-- `obtain`-friendly `pure` support resolver at the bare `OracleComp` level: `y ∈ support (pure
a)` forces `y = a`, matched by definitional unification (so it engages on the
`PFunctor.FreeM.pure` spelling that the syntactic `support_pure` `rw` rejects). -/
lemma eq_of_mem_support_pure (a : α) {y : α}
    (hy : y ∈ support (pure a : OracleComp spec α)) : y = a := by
  rwa [support_pure, Set.mem_singleton_iff] at hy

/-- `obtain`-friendly `<$>` (map) support peeler at the bare `OracleComp` level: `y ∈ support (g
<$> mx)` yields a preimage `a ∈ support mx` with `y = g a`, matched by definitional unification
(so it engages on the elaborated `Functor.map`/`OracleComp.instMonad` spelling that the syntactic
`support_map` `rw` rejects). -/
lemma mem_support_map_peel (g : α → β) (mx : OracleComp spec α) {y : β}
    (hy : y ∈ support (g <$> mx)) :
    ∃ a, a ∈ support mx ∧ y = g a := by
  rw [support_map, Set.mem_image] at hy
  obtain ⟨a, ha, hy⟩ := hy
  exact ⟨a, ha, hy.symm⟩

end supportPeel

end OracleComp

namespace OptionT

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Support-level peeler for an `OptionT`-monadic bind, stated at the underlying
`OracleComp`-level `.run`: every element `y` of the support of the *run* of `mx >>= f` factors
through an intermediate `some a` in `mx`'s run support and a `y` in the run support of `f a`,
unless `mx`'s run can produce `none` (in which case `y` may be that `none`). Companion to
`OptionT.mem_support_bind_mk` for the case where the `OptionT.run` has already been stripped to
the bare underlying computation.

Applies to a hypothesis `y ∈ support oa` whenever `oa` is *definitionally* `(mx >>= f).run`
(the `OptionT.run` is identity), so callers need not respell the full bind term. -/
lemma mem_support_run_bind
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((mx >>= f : OptionT (OracleComp spec) β).run)) :
    (none ∈ support mx.run ∧ y = none) ∨
      ∃ a, some a ∈ support mx.run ∧ y ∈ support ((f a).run) := by
  rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at hy
  obtain ⟨o, ho, hy⟩ := hy
  cases o with
  | none => exact Or.inl ⟨ho, by simpa using hy⟩
  | some a => exact Or.inr ⟨a, ho, hy⟩

/-- `OptionT.lift`-headed specialization of `mem_support_run_bind`: a `lift`ed (hence
never-failing) first computation `oa` peels cleanly, with the intermediate value living in
`support oa` directly (no `none` branch). -/
lemma mem_support_run_lift_bind
    (oa : OracleComp spec α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((OptionT.lift oa >>= f : OptionT (OracleComp spec) β).run)) :
    ∃ a, a ∈ support oa ∧ y ∈ support ((f a).run) := by
  rwa [OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_pure_comp, bind_map_left,
    mem_support_bind_iff] at hy

end OptionT
