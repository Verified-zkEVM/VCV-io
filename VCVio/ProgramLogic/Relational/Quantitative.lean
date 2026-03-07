/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.Basic
import VCVio.EvalDist.TVDist
import ToMathlib.ProbabilityTheory.OptimalCoupling

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
    classical
    letI : DecidableEq α := Classical.decEq α
    letI : DecidableEq β := Classical.decEq β
    unfold RelTriple' eRelTriple at h
    by_cases hne : Nonempty (SPMF.Coupling (evalDist oa) (evalDist ob))
    · let A := {a // a ∈ finSupport oa}
      let B := {b // b ∈ finSupport ob}
      letI : DecidableEq A := Classical.decEq A
      letI : DecidableEq B := Classical.decEq B
      letI : Fintype A := inferInstance
      letI : Fintype B := inferInstance
      have hA_nonempty : (finSupport oa).Nonempty := HasEvalPMF.finSupport_nonempty oa
      have hB_nonempty : (finSupport ob).Nonempty := HasEvalPMF.finSupport_nonempty ob
      let a₀ : A := ⟨hA_nonempty.choose, hA_nonempty.choose_spec⟩
      let b₀ : B := ⟨hB_nonempty.choose, hB_nonempty.choose_spec⟩
      let packA : α → A := fun a => if ha : a ∈ finSupport oa then ⟨a, ha⟩ else a₀
      let packB : β → B := fun b => if hb : b ∈ finSupport ob then ⟨b, hb⟩ else b₀
      let packPair : α × β → A × B := fun z => (packA z.1, packB z.2)
      let valPair : A × B → α × β := fun z => (z.1.1, z.2.1)
      let pa : SPMF A := packA <$> evalDist oa
      let pb : SPMF B := packB <$> evalDist ob
      have hvalA : Subtype.val <$> pa = evalDist oa := by
        apply SPMF.ext
        intro x
        change Pr[= x | Subtype.val <$> pa] = Pr[= x | evalDist oa]
        calc
          Pr[= x | Subtype.val <$> pa] = Pr[fun a : A => a.1 = x | pa] := by
            simpa using
              (probEvent_map (mx := pa) (f := Subtype.val) (q := fun y : α => y = x))
          _ = Pr[((fun a : A => a.1 = x) ∘ packA) | evalDist oa] := by
                rw [show pa = packA <$> evalDist oa by rfl]
                exact probEvent_map (mx := evalDist oa) (f := packA) (q := fun a : A => a.1 = x)
          _ = Pr[fun y : α => (packA y).1 = x | evalDist oa] := rfl
          _ = Pr[fun y : α => y = x | evalDist oa] := by
                apply probEvent_ext
                intro y hy
                have hyfin : y ∈ finSupport oa := by
                  exact mem_finSupport_of_mem_support_evalDist (oa := oa) (x := y) hy
                simp [packA, hyfin]
          _ = Pr[= x | evalDist oa] := by simp
      have hvalB : Subtype.val <$> pb = evalDist ob := by
        apply SPMF.ext
        intro y
        change Pr[= y | Subtype.val <$> pb] = Pr[= y | evalDist ob]
        calc
          Pr[= y | Subtype.val <$> pb] = Pr[fun b : B => b.1 = y | pb] := by
            simpa using
              (probEvent_map (mx := pb) (f := Subtype.val) (q := fun x : β => x = y))
          _ = Pr[((fun b : B => b.1 = y) ∘ packB) | evalDist ob] := by
                rw [show pb = packB <$> evalDist ob by rfl]
                exact probEvent_map (mx := evalDist ob) (f := packB) (q := fun b : B => b.1 = y)
          _ = Pr[fun x : β => (packB x).1 = y | evalDist ob] := rfl
          _ = Pr[fun x : β => x = y | evalDist ob] := by
                apply probEvent_ext
                intro x hx
                have hxfin : x ∈ finSupport ob := by
                  exact mem_finSupport_of_mem_support_evalDist (oa := ob) (x := x) hx
                simp [packB, hxfin]
          _ = Pr[= y | evalDist ob] := by simp
      have hsub_nonempty : Nonempty (SubPMF.Coupling pa pb) := by
        rcases hne with ⟨c₀⟩
        refine ⟨⟨packPair <$> c₀.1, ?_⟩⟩
        constructor
        · calc
            Prod.fst <$> (packPair <$> c₀.1) = packA <$> (Prod.fst <$> c₀.1) := by
              simp [packPair]
            _ = packA <$> evalDist oa := by rw [c₀.2.map_fst]
            _ = pa := rfl
        · calc
            Prod.snd <$> (packPair <$> c₀.1) = packB <$> (Prod.snd <$> c₀.1) := by
              simp [packPair]
            _ = packB <$> evalDist ob := by rw [c₀.2.map_snd]
            _ = pb := rfl
      let fSub : Option (A × B) → ℝ≥0∞
        | none => 0
        | some z => RelPost.indicator R z.1.1 z.2.1
      have hfSub : ∀ z, fSub z ≠ ⊤ := by
        intro z
        cases z with
        | none => simp [fSub]
        | some z =>
            by_cases hR : R z.1.1 z.2.1 <;> simp [fSub, RelPost.indicator, hR]
      obtain ⟨cMaxSub, hMaxSub⟩ := SubPMF.exists_max_coupling
        (p := pa) (q := pb) fSub hfSub hsub_nonempty
      have hsub_obj :
          ∀ c : SubPMF.Coupling pa pb,
            (∑' z : Option (A × B), c.1.1 z * fSub z) =
              Pr[fun z : A × B => R z.1.1 z.2.1 | (c.1 : SubPMF (A × B))] := by
        intro c
        rw [probEvent_eq_tsum_ite, tsum_option _ ENNReal.summable]
        simp [fSub, RelPost.indicator]
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases hR : R x.1.1 x.2.1
        · simp [hR, OptionT.probOutput_eq, PMF.probOutput_eq_apply]
          rfl
        · simp [hR]
      have hlift_obj :
          ∀ c : SPMF.Coupling (evalDist oa) (evalDist ob),
            Pr[fun z : A × B => R z.1.1 z.2.1 | packPair <$> c.1] =
              Pr[fun z : α × β => R z.1 z.2 | c.1] := by
        intro c
        rw [probEvent_map]
        apply probEvent_ext
        intro z hz
        have hzfst : z.1 ∈ support (Prod.fst <$> c.1) := by
          rw [support_map]
          exact ⟨z, hz, rfl⟩
        have hzsnd : z.2 ∈ support (Prod.snd <$> c.1) := by
          rw [support_map]
          exact ⟨z, hz, rfl⟩
        have hzfst' : z.1 ∈ finSupport oa := by
          rw [c.2.map_fst] at hzfst
          exact mem_finSupport_of_mem_support_evalDist (oa := oa) (x := z.1) hzfst
        have hzsnd' : z.2 ∈ finSupport ob := by
          rw [c.2.map_snd] at hzsnd
          exact mem_finSupport_of_mem_support_evalDist (oa := ob) (x := z.2) hzsnd
        simp [packPair, packA, packB, hzfst', hzsnd']
      have hpush :
          SPMF.IsCoupling (valPair <$> cMaxSub.1) (evalDist oa) (evalDist ob) := by
        constructor
        · simpa [valPair] using
            (congrArg (fun p : SPMF A => Subtype.val <$> p) cMaxSub.2.map_fst).trans hvalA
        · simpa [valPair] using
            (congrArg (fun p : SPMF B => Subtype.val <$> p) cMaxSub.2.map_snd).trans hvalB
      let cMaxSub' : SPMF.Coupling pa pb := ⟨cMaxSub.1, cMaxSub.2⟩
      let cMax : SPMF.Coupling (evalDist oa) (evalDist ob) := ⟨valPair <$> cMaxSub.1, hpush⟩
      have hpush_obj :
          Pr[fun z : α × β => R z.1 z.2 | cMax.1] =
            Pr[fun z : A × B => R z.1.1 z.2.1 | cMaxSub'.1] := by
        change Pr[fun z : α × β => R z.1 z.2 | valPair <$> cMaxSub'.1] =
          Pr[((fun z : α × β => R z.1 z.2) ∘ valPair) | cMaxSub'.1]
        exact probEvent_map (mx := cMaxSub'.1) (f := valPair)
          (q := fun z : α × β => R z.1 z.2)
      have hpush_obj' :
          Pr[fun z : α × β => R z.1 z.2 | cMax.1] =
            Pr[fun z : A × B => R z.1.1 z.2.1 | (cMaxSub.1 : SubPMF (A × B))] := by
        change
          @probEvent SPMF SPMF.instAlternativeMonad.toMonad (α × β) SPMF.instHasEvalSPMF
              cMax.1 (fun z : α × β => R z.1 z.2) =
            @probEvent SubPMF OptionT.instMonad (A × B) (OptionT.instHasEvalSPMF PMF)
              (cMaxSub.1 : SubPMF (A × B))
              (fun z : A × B => R z.1.1 z.2.1)
        calc
          @probEvent SPMF SPMF.instAlternativeMonad.toMonad (α × β) SPMF.instHasEvalSPMF
              cMax.1 (fun z : α × β => R z.1 z.2)
              =
            @probEvent SPMF SPMF.instAlternativeMonad.toMonad (A × B) SPMF.instHasEvalSPMF
              cMaxSub'.1 (fun z : A × B => R z.1.1 z.2.1) :=
                hpush_obj
          _ =
            @probEvent SPMF SPMF.instAlternativeMonad.toMonad (A × B) SPMF.instHasEvalSPMF
              cMaxSub.1 (fun z : A × B => R z.1.1 z.2.1) := by
                rfl
          _ =
            @probEvent SubPMF OptionT.instMonad (A × B) (OptionT.instHasEvalSPMF PMF)
              (cMaxSub.1 : SubPMF (A × B))
              (fun z : A × B => R z.1.1 z.2.1) :=
                (OptionT.probEvent_subpmf_eq_spmf cMaxSub.1 (fun z : A × B => R z.1.1 z.2.1)).symm
      have hsub_le_max :
          ∀ c : SubPMF.Coupling pa pb,
            Pr[fun z : A × B => R z.1.1 z.2.1 | (c.1 : SubPMF (A × B))] ≤
              Pr[fun z : A × B => R z.1.1 z.2.1 | (cMaxSub.1 : SubPMF (A × B))] := by
        intro c
        have hle :
            (∑' z : Option (A × B), c.1.1 z * fSub z) ≤
              (∑' z : Option (A × B), cMaxSub.1.1 z * fSub z) := by
          calc
            (∑' z : Option (A × B), c.1.1 z * fSub z)
                ≤ (⨆ c' : SubPMF.Coupling pa pb, ∑' z : Option (A × B), c'.1.1 z * fSub z) :=
                  le_iSup (f := fun c' : SubPMF.Coupling pa pb =>
                    ∑' z : Option (A × B), c'.1.1 z * fSub z) c
            _ = (∑' z : Option (A × B), cMaxSub.1.1 z * fSub z) := hMaxSub
        rw [hsub_obj c, hsub_obj cMaxSub] at hle
        exact hle
      have hupper :
          eRelWP oa ob (RelPost.indicator R) ≤
            Pr[fun z : α × β => R z.1 z.2 | cMax.1] := by
        unfold eRelWP
        refine iSup_le ?_
        intro c
        let cLift : SubPMF.Coupling pa pb := ⟨packPair <$> c.1, by
          constructor
          · calc
              Prod.fst <$> (packPair <$> c.1) = packA <$> (Prod.fst <$> c.1) := by
                simp [packPair]
              _ = packA <$> evalDist oa := by rw [c.2.map_fst]
              _ = pa := rfl
          · calc
              Prod.snd <$> (packPair <$> c.1) = packB <$> (Prod.snd <$> c.1) := by
                simp [packPair]
              _ = packB <$> evalDist ob := by rw [c.2.map_snd]
              _ = pb := rfl⟩
        calc
          ∑' z, Pr[= z | c.1] * RelPost.indicator R z.1 z.2
              = Pr[fun z : α × β => R z.1 z.2 | c.1] := by
                  simpa [RelPost.indicator] using indicator_objective_eq_probEvent (mx := c.1) (R := R)
          _ = Pr[fun z : A × B => R z.1.1 z.2.1 | packPair <$> c.1] := by
                exact (hlift_obj c).symm
          _ = Pr[fun z : A × B => R z.1.1 z.2.1 | (packPair <$> c.1 : SubPMF (A × B))] := by
                exact (OptionT.probEvent_subpmf_eq_spmf (packPair <$> c.1)
                  (fun z : A × B => R z.1.1 z.2.1)).symm
          _ = Pr[fun z : A × B => R z.1.1 z.2.1 | (cLift.1 : SubPMF (A × B))] := by
                rfl
          _ ≤ Pr[fun z : A × B => R z.1.1 z.2.1 | cMaxSub.1] := hsub_le_max cLift
          _ = Pr[fun z : α × β => R z.1 z.2 | cMax.1] := hpush_obj'.symm
      have hmax_ge : 1 ≤ Pr[fun z : α × β => R z.1 z.2 | cMax.1] := le_trans h hupper
      have hmax_eq : Pr[fun z : α × β => R z.1 z.2 | cMax.1] = 1 :=
        le_antisymm probEvent_le_one hmax_ge
      exact ⟨cMax, (probEvent_eq_one_iff (mx := cMax.1) (p := fun z : α × β => R z.1 z.2)).1 hmax_eq |>.2⟩
    · exfalso
      haveI : IsEmpty (SPMF.Coupling (evalDist oa) (evalDist ob)) := not_nonempty_iff.mp hne
      rw [eRelWP, iSup_of_empty] at h
      exact not_le_of_gt zero_lt_one h
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
  unfold eRelTriple at h ⊢
  refine le_trans hpre (le_trans h ?_)
  unfold eRelWP
  refine iSup_le fun c => ?_
  exact le_trans
    (ENNReal.tsum_le_tsum fun z : α × β => mul_le_mul' le_rfl (hpost z.1 z.2))
    (le_iSup (f := fun c' : SPMF.Coupling (evalDist oa) (evalDist ob) =>
      ∑' z : α × β, Pr[= z | c'.1] * post' z.1 z.2) c)

/-- Bind/sequential composition rule for eRHL. -/
theorem eRelTriple_bind
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {cut : α → β → ℝ≥0∞} {post : γ → δ → ℝ≥0∞}
    (hxy : eRelTriple pre oa ob cut)
    (hfg : ∀ a b, eRelTriple (cut a b) (fa a) (fb b) post) :
    eRelTriple pre (oa >>= fa) (ob >>= fb) post := by
  -- Blocked: the natural gluing proof uses `_root_.SPMF.IsCoupling.bind`, but to
  -- commute the outer weighted sum with the inner `iSup` we need a finite
  -- enumeration of the outer coupling support. `OracleComp` exposes `finSupport`,
  -- but generic `SPMF` couplings do not currently expose `HasEvalFinset`, so the
  -- straightforward `probOutput_bind_eq_sum_finSupport` route is unavailable here.
  -- A complete proof seems to require either:
  -- 1. a finite-support API for `SPMF` couplings whose marginals are finitely supported, or
  -- 2. redoing the bridge theorem's packing argument to reduce the outer coupling to
  --    a finite subtype before commuting the finite sum with the inner `iSup`.
  sorry

/-! ## Statistical distance via eRHL -/

/-- Statistical distance as a complement of eRHL value with equality indicator.
Uses `SPMF.tvDist` directly to handle cross-spec comparison. -/
theorem spmf_tvDist_eq_one_sub_eRelWP_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    SPMF.tvDist (evalDist oa) (evalDist ob) =
      (1 - eRelWP oa ob (RelPost.indicator (EqRel α))).toReal := by
  -- Blocked: this needs a theorem identifying `SPMF.tvDist` with
  -- `1 - sup_c Pr[z.1 = z.2 | c]` over couplings `c`.
  -- `ToMathlib/ProbabilityTheory/OptimalCoupling.lean` gives maximizers for bounded
  -- coupling objectives, but the repo does not yet provide the TV/coupling
  -- identification theorem itself.
  sorry

/-- Same-spec version using the `tvDist` notation. -/
theorem tvDist_eq_one_sub_eRelWP_eqRel
    {oa ob : OracleComp spec₁ α} :
    tvDist oa ob = (1 - eRelWP (spec₂ := spec₁) oa ob
      (RelPost.indicator (EqRel α))).toReal := by
  simpa [tvDist] using
    (spmf_tvDist_eq_one_sub_eRelWP_eqRel
      (spec₁ := spec₁) (spec₂ := spec₁) (oa := oa) (ob := ob))

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
