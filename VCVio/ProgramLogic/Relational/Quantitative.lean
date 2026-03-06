/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Basic
import VCVio.EvalDist.TVDist

/-!
# Quantitative Relational Program Logic (eRHL)

This file defines the eRHL-style quantitative relational logic for `OracleComp`.

The core idea (from Avanzini-Barthe-Gregoire-Davoli, POPL 2025) is to make pre/postconditions
`ℝ≥0∞`-valued instead of `Prop`-valued. This subsumes both pRHL (exact coupling, via indicator
postconditions) and apRHL (ε-approximate coupling, via threshold preconditions).

## Main definitions

- `eRelWP`: quantitative relational WP — supremum over couplings of expected postcondition
- `eRelTriple`: quantitative relational triple (`pre ≤ eRelWP oa ob post`)
- `RelPost.indicator`: indicator postcondition lifting `Prop` to `ℝ≥0∞`
- `RelTriple'`: pRHL-style exact coupling as eRHL special case
- `ApproxRelTriple`: apRHL-style ε-approximate coupling as eRHL special case

## Design

```
                eRHL (ℝ≥0∞-valued pre/post)
               /          |           \
              /           |            \
pRHL (exact)    apRHL (ε-approx)   stat-distance
indicator R      1-ε, indicator R    1, indicator(=)
```
-/

open scoped Classical
open ENNReal OracleSpec OracleComp

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

/-! ## Helpers for coupling mass -/

private lemma coupling_probFailure_eq_zero
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (c : SPMF.Coupling (evalDist oa) (evalDist ob)) :
    Pr[⊥ | c.1] = 0 := by
  have h1 : Pr[⊥ | Prod.fst <$> c.1] = Pr[⊥ | c.1] :=
    probFailure_map (f := Prod.fst) (mx := c.1)
  rw [c.2.map_fst] at h1
  rw [← h1]
  change (evalDist oa).toPMF none = 0
  exact probFailure_eq_zero (mx := oa)

private lemma coupling_tsum_probOutput_eq_one
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (c : SPMF.Coupling (evalDist oa) (evalDist ob)) :
    ∑' z : α × β, Pr[= z | c.1] = 1 := by
  rw [tsum_probOutput_eq_sub, coupling_probFailure_eq_zero c, tsub_zero]

/-! ## Core eRHL definitions -/

/-- eRHL-style quantitative relational WP for `OracleComp`.
`eRelWP oa ob g` = supremum over all couplings `c` of `E_c[g(a,b)]`.
This is the expected value of postcondition `g` under the optimal coupling. -/
noncomputable def eRelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (g : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (c : SPMF.Coupling (evalDist oa) (evalDist ob)),
    ∑' z, Pr[= z | c.1] * g z.1 z.2

/-- eRHL triple: `pre ≤ eRelWP oa ob post`. -/
def eRelTriple (pre : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) : Prop :=
  pre ≤ eRelWP oa ob post

/-! ## Indicator postconditions: bridge from Prop to ℝ≥0∞ -/

/-- Indicator postcondition: lifts a `Prop`-valued relation to an `ℝ≥0∞`-valued one. -/
noncomputable def RelPost.indicator (R : α → β → Prop) : α → β → ℝ≥0∞ :=
  fun a b => if R a b then 1 else 0

/-! ## pRHL as a special case of eRHL -/

/-- pRHL-style exact relational triple, defined via eRHL with indicator postcondition.
Equivalent to the existing coupling-based `CouplingPost`. -/
def RelTriple' (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  eRelTriple 1 oa ob (RelPost.indicator R)

/-- Bridge: the eRHL-based definition agrees with the existing coupling-based one.

**Forward direction blocker**: `RelTriple' → CouplingPost` requires extracting a coupling `c`
with `f(c) = 1` from `1 ≤ ⨆ c, f(c)`. Although the coupling polytope is compact and `f` is
linear (so the max IS attained in standard math), formalizing this in Lean requires proving
compactness of the coupling space, which needs topology infrastructure not yet available here. -/
theorem relTriple'_iff_couplingPost
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ CouplingPost oa ob R := by
  constructor
  · intro h
    -- Forward: RelTriple' → CouplingPost
    -- 1 ≤ ⨆ c, ∑' z, Pr[= z | c.1] * indicator R z.1 z.2 → ∃ c, ∀ z ∈ support c.1, R z.1 z.2
    -- Requires extracting a maximizer from the iSup (coupling compactness).
    sorry
  · intro ⟨c, hc⟩
    -- Backward: CouplingPost → RelTriple'
    unfold RelTriple' eRelTriple eRelWP
    apply le_iSup_of_le c
    suffices h : ∑' z, Pr[= z | c.1] * RelPost.indicator R z.1 z.2 = 1 by rw [h]
    have heq : ∀ z : α × β,
        Pr[= z | c.1] * RelPost.indicator R z.1 z.2 = Pr[= z | c.1] := by
      intro z
      by_cases hz : z ∈ support c.1
      · simp [RelPost.indicator, hc z hz, mul_one]
      · simp [probOutput_eq_zero_of_not_mem_support hz]
    simp_rw [heq]
    exact coupling_tsum_probOutput_eq_one c

/-- Bridge: `RelTriple'` agrees with the existing `RelTriple`. -/
theorem relTriple'_iff_relTriple
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ RelTriple oa ob R := by
  rw [relTriple'_iff_couplingPost, relTriple_iff_relWP, relWP_iff_couplingPost]

/-! ## apRHL as a special case of eRHL -/

/-- ε-approximate relational triple via eRHL:
"R holds except with probability at most ε." -/
def ApproxRelTriple (ε : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  eRelTriple (1 - ε) oa ob (RelPost.indicator R)

/-- Exact coupling is the zero-error special case of approximate coupling. -/
theorem relTriple'_eq_approxRelTriple_zero
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ ApproxRelTriple 0 oa ob R := by
  simp [RelTriple', ApproxRelTriple]

/-! ## eRHL rules -/

/-- Pure rule for eRHL. -/
theorem eRelTriple_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    eRelTriple (post a b) (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post := by
  unfold eRelTriple eRelWP
  have hc : SPMF.IsCoupling (pure (a, b) : SPMF (α × β))
      (evalDist (pure a : OracleComp spec₁ α)) (evalDist (pure b : OracleComp spec₂ β)) := by
    simp [evalDist_pure]; exact SubPMF.IsCoupling.pure_iff.mpr rfl
  apply le_iSup_of_le ⟨pure (a, b), hc⟩
  have key : ∑' z, Pr[= z | (pure (a, b) : SPMF (α × β))] * post z.1 z.2 = post a b := by
    rw [tsum_eq_single (a, b)]
    · simp [SPMF.probOutput_eq_apply]
    · intro z hz
      have : Pr[= z | (pure (a, b) : SPMF (α × β))] = 0 := by
        rw [SPMF.probOutput_eq_apply]; simp [hz]
      simp [this]
  exact key ▸ le_refl _

/-- Monotonicity/consequence rule for eRHL. -/
theorem eRelTriple_conseq {pre pre' : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ a b, post a b ≤ post' a b)
    (h : eRelTriple pre oa ob post) :
    eRelTriple pre' oa ob post' := by
  sorry

/-- Bind/sequential composition rule for eRHL. -/
theorem eRelTriple_bind
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {cut : α → β → ℝ≥0∞} {post : γ → δ → ℝ≥0∞}
    (hxy : eRelTriple pre oa ob cut)
    (hfg : ∀ a b, eRelTriple (cut a b) (fa a) (fb b) post) :
    eRelTriple pre (oa >>= fa) (ob >>= fb) post := by
  sorry

/-! ## Statistical distance via eRHL -/

/-- Statistical distance as a complement of eRHL value with equality indicator.
Uses `SPMF.tvDist` directly to handle cross-spec comparison. -/
theorem spmf_tvDist_eq_one_sub_eRelWP_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    SPMF.tvDist (evalDist oa) (evalDist ob) =
      (1 - eRelWP oa ob (RelPost.indicator (EqRel α))).toReal := by
  sorry

/-- Same-spec version using the `tvDist` notation. -/
theorem tvDist_eq_one_sub_eRelWP_eqRel
    {oa ob : OracleComp spec₁ α} :
    tvDist oa ob = (1 - eRelWP (spec₂ := spec₁) oa ob
      (RelPost.indicator (EqRel α))).toReal := by
  sorry

/-! ## pRHL convenience rules (Prop-level, no ℝ≥0∞ visible) -/

/-- Bind for pRHL exact coupling. -/
lemma relTriple'_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple' oa ob R)
    (hfg : ∀ a b, R a b → RelTriple' (fa a) (fb b) S) :
    RelTriple' (oa >>= fa) (ob >>= fb) S := by
  rw [relTriple'_iff_relTriple] at hxy ⊢
  exact relTriple_bind hxy (fun a b hab => relTriple'_iff_relTriple.mp (hfg a b hab))

/-- Game equivalence from pRHL equality coupling. -/
theorem gameEquiv_of_relTriple'_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple' oa ob (EqRel α)) :
    evalDist oa = evalDist ob := by
  exact evalDist_eq_of_relTriple_eqRel (relTriple'_iff_relTriple.mp h)

end OracleComp.ProgramLogic.Relational
