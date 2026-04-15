/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.QuantitativeDefs
import VCVio.EvalDist.TVDist

/-!
# Quantitative Relational Program Logic (eRHL)

This file develops the main theorem layer for the eRHL-style quantitative relational
logic for `OracleComp`, building on the core interfaces in
`VCVio.ProgramLogic.Relational.QuantitativeDefs`.

The core idea (from Avanzini-Barthe-Gregoire-Davoli, POPL 2025) is to make pre/postconditions
`ℝ≥0∞`-valued instead of `Prop`-valued. This subsumes both pRHL (exact coupling, via indicator
postconditions) and apRHL (ε-approximate coupling, via threshold preconditions).

## Main results in this file

- coupling-mass lemmas and support facts
- introduction, consequence, and bind rules for eRHL
- bridges to exact and approximate couplings
- total-variation characterizations via `EqRel`

## Design

```
                eRHL (ℝ≥0∞-valued pre/post)
               /          |           \
              /           |            \
pRHL (exact)    apRHL (ε-approx)   stat-distance
indicator R      1-ε, indicator R    1, indicator(=)
```
-/

set_option linter.style.openClassical false
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

private lemma spmf_bind_const_of_no_failure {p : SPMF α} (hp : Pr[⊥ | p] = 0) (q : SPMF β) :
    (p >>= fun _ => q) = q := by
  apply SPMF.ext; intro y
  change Pr[= y | p >>= fun _ => q] = Pr[= y | q]
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, hp,
    tsub_zero, one_mul]

private lemma nonempty_spmf_coupling
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} :
    Nonempty (SPMF.Coupling (evalDist oa) (evalDist ob)) := by
  let p := evalDist oa
  let q := evalDist ob
  have hp : Pr[⊥ | p] = 0 := by
    change (evalDist oa).toPMF none = 0; exact probFailure_eq_zero (mx := oa)
  have hq : Pr[⊥ | q] = 0 := by
    change (evalDist ob).toPMF none = 0; exact probFailure_eq_zero (mx := ob)
  let c : SPMF (α × β) := p >>= fun (a : α) => q >>= fun (b : β) => pure (a, b)
  refine ⟨⟨c, ?_, ?_⟩⟩
  · change Prod.fst <$> c = p
    simp only [c, map_bind, map_pure]
    conv_rhs => rw [← bind_pure p]
    congr 1; funext a
    exact spmf_bind_const_of_no_failure hq (pure a)
  · change Prod.snd <$> c = q
    simp only [c, map_bind, map_pure]
    have : (fun (_ : α) => q >>= fun (b : β) => pure b) = fun _ => q := by
      funext _; exact bind_pure q
    rw [this]
    exact spmf_bind_const_of_no_failure hp q

set_option linter.unusedDecidableInType false
-- TODO: move to ToMathlib
private lemma Finset_sum_iSup_le_iSup_sum {ι : Type*} {J : ι → Type*}
    [DecidableEq ι] [hne : ∀ i, Nonempty (J i)]
    (g : (i : ι) → J i → ℝ≥0∞) (s : Finset ι) :
    ∑ i ∈ s, ⨆ j, g i j ≤ ⨆ (f : ∀ i, J i), ∑ i ∈ s, g i (f i) := by
  haveI : Nonempty (∀ i, J i) := ⟨fun i => (hne i).some⟩
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  simp_rw [Finset.sum_insert ha]
  calc (⨆ j, g a j) + ∑ i ∈ s, ⨆ j, g i j
      ≤ (⨆ j, g a j) + ⨆ (f : ∀ i, J i), ∑ i ∈ s, g i (f i) :=
        add_le_add le_rfl ih
    _ = ⨆ j, ⨆ (f : ∀ i, J i), (g a j + ∑ i ∈ s, g i (f i)) := by
        rw [ENNReal.iSup_add]; congr 1; ext j; rw [ENNReal.add_iSup]
    _ ≤ ⨆ (f : ∀ i, J i), (g a (f a) + ∑ i ∈ s, g i (f i)) := by
        refine iSup_le fun j => iSup_le fun f => ?_
        refine le_iSup_of_le (Function.update f a j) (le_of_eq ?_)
        rw [Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]

private lemma ENNReal_tsum_iSup_le {ι : Type*} {J : ι → Type*}
    [∀ i, Nonempty (J i)] (g : (i : ι) → J i → ℝ≥0∞) :
    ∑' i, ⨆ j, g i j ≤ ⨆ (f : ∀ i, J i), ∑' i, g i (f i) := by
  letI : DecidableEq ι := Classical.decEq ι
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => le_trans (Finset_sum_iSup_le_iSup_sum g s) ?_
  exact iSup_mono fun f => ENNReal.sum_le_tsum _

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
          Pr[= x | Subtype.val <$> pa] = Pr[ fun a : A => a.1 = x | pa] := by
            simpa using
              (probEvent_map (mx := pa) (f := Subtype.val) (q := fun y : α => y = x))
          _ = Pr[ ((fun a : A => a.1 = x) ∘ packA) | evalDist oa] := by
                rw [show pa = packA <$> evalDist oa by rfl]
                exact probEvent_map (mx := evalDist oa) (f := packA) (q := fun a : A => a.1 = x)
          _ = Pr[ fun y : α => (packA y).1 = x | evalDist oa] := rfl
          _ = Pr[ fun y : α => y = x | evalDist oa] := by
                apply probEvent_ext
                intro y hy
                have hyfin : y ∈ finSupport oa :=
                  mem_finSupport_of_mem_support_evalDist (oa := oa) (x := y) hy
                simp [packA, hyfin]
          _ = Pr[= x | evalDist oa] := by simp
      have hvalB : Subtype.val <$> pb = evalDist ob := by
        apply SPMF.ext
        intro y
        change Pr[= y | Subtype.val <$> pb] = Pr[= y | evalDist ob]
        calc
          Pr[= y | Subtype.val <$> pb] = Pr[ fun b : B => b.1 = y | pb] := by
            simpa using
              (probEvent_map (mx := pb) (f := Subtype.val) (q := fun x : β => x = y))
          _ = Pr[ ((fun b : B => b.1 = y) ∘ packB) | evalDist ob] := by
                rw [show pb = packB <$> evalDist ob by rfl]
                exact probEvent_map (mx := evalDist ob) (f := packB) (q := fun b : B => b.1 = y)
          _ = Pr[ fun x : β => (packB x).1 = y | evalDist ob] := rfl
          _ = Pr[ fun x : β => x = y | evalDist ob] := by
                apply probEvent_ext
                intro x hx
                have hxfin : x ∈ finSupport ob :=
                  mem_finSupport_of_mem_support_evalDist (oa := ob) (x := x) hx
                simp [packB, hxfin]
          _ = Pr[= y | evalDist ob] := by simp
      have hsub_nonempty : Nonempty (SPMF.Coupling pa pb) := by
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
      obtain ⟨cMaxSub, hMaxSub⟩ := SPMF.exists_max_coupling
        (p := pa) (q := pb) fSub hfSub hsub_nonempty
      have hsub_obj :
          ∀ c : SPMF.Coupling pa pb,
            (∑' z : Option (A × B), c.1.1 z * fSub z) =
              Pr[ fun z : A × B => R z.1.1 z.2.1 | (c.1 : SPMF (A × B))] := by
        intro c
        rw [probEvent_eq_tsum_ite, tsum_option _ ENNReal.summable]
        simp only [RelPost.indicator, mul_zero, mul_ite, mul_one, tsum_fintype, zero_add, fSub]
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases hR : R x.1.1 x.2.1
        · rfl
        · simp [hR]
      have hlift_obj :
          ∀ c : SPMF.Coupling (evalDist oa) (evalDist ob),
            Pr[ fun z : A × B => R z.1.1 z.2.1 | packPair <$> c.1] =
              Pr[ fun z : α × β => R z.1 z.2 | c.1] := by
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
          Pr[ fun z : α × β => R z.1 z.2 | cMax.1] =
            Pr[ fun z : A × B => R z.1.1 z.2.1 | cMaxSub'.1] := by
        change Pr[ fun z : α × β => R z.1 z.2 | valPair <$> cMaxSub'.1] =
          Pr[ ((fun z : α × β => R z.1 z.2) ∘ valPair) | cMaxSub'.1]
        exact probEvent_map (mx := cMaxSub'.1) (f := valPair)
          (q := fun z : α × β => R z.1 z.2)
      have hsub_le_max :
          ∀ c : SPMF.Coupling pa pb,
            Pr[ fun z : A × B => R z.1.1 z.2.1 | (c.1 : SPMF (A × B))] ≤
              Pr[ fun z : A × B => R z.1.1 z.2.1 | (cMaxSub.1 : SPMF (A × B))] := by
        intro c
        have hle :
            (∑' z : Option (A × B), c.1.1 z * fSub z) ≤
              (∑' z : Option (A × B), cMaxSub.1.1 z * fSub z) := by
          calc
            (∑' z : Option (A × B), c.1.1 z * fSub z)
                ≤ (⨆ c' : SPMF.Coupling pa pb, ∑' z : Option (A × B), c'.1.1 z * fSub z) :=
                  le_iSup (f := fun c' : SPMF.Coupling pa pb =>
                    ∑' z : Option (A × B), c'.1.1 z * fSub z) c
            _ = (∑' z : Option (A × B), cMaxSub.1.1 z * fSub z) := hMaxSub
        rw [hsub_obj c, hsub_obj cMaxSub] at hle
        exact hle
      have hupper :
          eRelWP oa ob (RelPost.indicator R) ≤
            Pr[ fun z : α × β => R z.1 z.2 | cMax.1] := by
        unfold eRelWP
        refine iSup_le ?_
        intro c
        let cLift : SPMF.Coupling pa pb := ⟨packPair <$> c.1, by
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
              = Pr[ fun z : α × β => R z.1 z.2 | c.1] := by
                  simpa [RelPost.indicator] using
                    indicator_objective_eq_probEvent (mx := c.1) (R := R)
          _ = Pr[ fun z : A × B => R z.1.1 z.2.1 | packPair <$> c.1] :=
                (hlift_obj c).symm
          _ ≤ Pr[ fun z : α × β => R z.1 z.2 | cMax.1] := by
            rw [hpush_obj]
            refine le_of_eq_of_le ?_ (hsub_le_max cLift)
            rw [hlift_obj]
      have hmax_ge : 1 ≤ Pr[ fun z : α × β => R z.1 z.2 | cMax.1] := le_trans h hupper
      have hmax_eq : Pr[ fun z : α × β => R z.1 z.2 | cMax.1] = 1 :=
        le_antisymm probEvent_le_one hmax_ge
      exact ⟨cMax,
        (probEvent_eq_one_iff (mx := cMax.1) (p := fun z : α × β => R z.1 z.2)).1 hmax_eq |>.2⟩
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

/-- If a `RelTriple'` holds for `fun a b => f a = g b`, then mapping by `f` and `g`
produces equal distributions. This is the eRHL-level version of
`evalDist_map_eq_of_relTriple`. -/
lemma evalDist_map_eq_of_relTriple' {σ : Type}
    {f : α → σ} {g : β → σ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple' oa ob (fun a b => f a = g b)) :
    evalDist (f <$> oa) = evalDist (g <$> ob) :=
  evalDist_map_eq_of_relTriple (relTriple'_iff_relTriple.mp h)

/-! ## eRHL rules -/

/-- Pure rule for eRHL. -/
theorem eRelTriple_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    eRelTriple (post a b) (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post := by
  unfold eRelTriple eRelWP
  have hc : SPMF.IsCoupling (pure (a, b) : SPMF (α × β))
      (evalDist (pure a : OracleComp spec₁ α)) (evalDist (pure b : OracleComp spec₂ β)) := by
    simpa only [evalDist_pure] using SPMF.IsCoupling.pure_iff.mpr rfl
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
  have hstep : eRelTriple pre oa ob (fun a b => eRelWP (fa a) (fb b) post) :=
    eRelTriple_conseq le_rfl (fun a b => hfg a b) hxy
  change pre ≤ eRelWP (oa >>= fa) (ob >>= fb) post
  refine le_trans hstep ?_
  show eRelWP oa ob (fun a b => eRelWP (fa a) (fb b) post) ≤
    eRelWP (oa >>= fa) (ob >>= fb) post
  unfold eRelWP
  refine iSup_le fun c => ?_
  have hne : ∀ a b, Nonempty (SPMF.Coupling (evalDist (fa a)) (evalDist (fb b))) :=
    fun a b => nonempty_spmf_coupling
  calc ∑' z, Pr[= z | c.1] *
        (⨆ d : SPMF.Coupling (evalDist (fa z.1)) (evalDist (fb z.2)),
          ∑' w, Pr[= w | d.1] * post w.1 w.2)
      = ∑' z, ⨆ d : SPMF.Coupling (evalDist (fa z.1)) (evalDist (fb z.2)),
          Pr[= z | c.1] * (∑' w, Pr[= w | d.1] * post w.1 w.2) := by
        congr 1; ext z; exact ENNReal.mul_iSup ..
    _ ≤ ⨆ (D : ∀ z : α × β,
            SPMF.Coupling (evalDist (fa z.1)) (evalDist (fb z.2))),
          ∑' z, Pr[= z | c.1] * (∑' w, Pr[= w | (D z).1] * post w.1 w.2) :=
        ENNReal_tsum_iSup_le _
    _ ≤ ⨆ c' : SPMF.Coupling (evalDist (oa >>= fa)) (evalDist (ob >>= fb)),
          ∑' w, Pr[= w | c'.1] * post w.1 w.2 := by
        refine iSup_le fun D => ?_
        let d : α → β → SPMF (γ × δ) := fun a b => (D (a, b)).1
        have hd : ∀ a b, c.1.1 (some (a, b)) ≠ 0 →
            SPMF.IsCoupling (d a b) (evalDist (fa a)) (evalDist (fb b)) :=
          fun a b _ => (D (a, b)).2
        have hglue : SPMF.IsCoupling (c.1 >>= fun p => d p.1 p.2)
            (evalDist oa >>= fun a => evalDist (fa a))
            (evalDist ob >>= fun b => evalDist (fb b)) :=
          SPMF.IsCoupling.bind c d hd
        let c' : SPMF.Coupling (evalDist (oa >>= fa)) (evalDist (ob >>= fb)) :=
          ⟨c.1 >>= fun p => d p.1 p.2, by rwa [evalDist_bind, evalDist_bind]⟩
        apply le_iSup_of_le c'
        suffices h : ∑' z, Pr[= z | c.1] * (∑' w, Pr[= w | d z.1 z.2] * post w.1 w.2) =
            ∑' w, Pr[= w | c'.1] * post w.1 w.2 from h ▸ le_refl _
        have hbind : ∀ w : γ × δ,
            Pr[= w | c'.1] = ∑' z : α × β, Pr[= z | c.1] * Pr[= w | d z.1 z.2] :=
          fun w => probOutput_bind_eq_tsum c.1 (fun p => d p.1 p.2) w
        simp_rw [hbind]
        calc ∑' z, Pr[= z | c.1] * (∑' w, Pr[= w | d z.1 z.2] * post w.1 w.2)
            = ∑' z, ∑' w, Pr[= z | c.1] * (Pr[= w | d z.1 z.2] * post w.1 w.2) := by
              congr 1; ext z; rw [ENNReal.tsum_mul_left]
          _ = ∑' z, ∑' w, Pr[= z | c.1] * Pr[= w | d z.1 z.2] * post w.1 w.2 := by
              congr 1; ext z; congr 1; ext w; ring
          _ = ∑' w, ∑' z, Pr[= z | c.1] * Pr[= w | d z.1 z.2] * post w.1 w.2 :=
              ENNReal.tsum_comm
          _ = ∑' w, (∑' z, Pr[= z | c.1] * Pr[= w | d z.1 z.2]) * post w.1 w.2 := by
              congr 1; ext w; rw [ENNReal.tsum_mul_right]

/-! ## Helpers for statistical distance / coupling characterization -/

private lemma probOutput_diag_le_min_marginals
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (c : SPMF.Coupling (evalDist oa) (evalDist ob)) (a : α) :
    Pr[= (a, a) | c.1] ≤ min (Pr[= a | evalDist oa]) (Pr[= a | evalDist ob]) := by
  refine le_min ?_ ?_
  · calc Pr[= (a, a) | c.1]
        = Pr[ (· = (a, a)) | c.1] := (probEvent_eq_eq_probOutput c.1 (a, a)).symm
      _ ≤ Pr[ (· = a) ∘ Prod.fst | c.1] :=
          probEvent_mono fun z _ h => h ▸ rfl
      _ = Pr[ (· = a) | Prod.fst <$> c.1] :=
          (probEvent_map c.1 Prod.fst (· = a)).symm
      _ = Pr[= a | evalDist oa] := by
          rw [probEvent_eq_eq_probOutput, c.2.map_fst]
  · calc Pr[= (a, a) | c.1]
        = Pr[ (· = (a, a)) | c.1] := (probEvent_eq_eq_probOutput c.1 (a, a)).symm
      _ ≤ Pr[ (· = a) ∘ Prod.snd | c.1] :=
          probEvent_mono fun z _ h => h ▸ rfl
      _ = Pr[ (· = a) | Prod.snd <$> c.1] :=
          (probEvent_map c.1 Prod.snd (· = a)).symm
      _ = Pr[= a | evalDist ob] := by
          rw [probEvent_eq_eq_probOutput, c.2.map_snd]

private lemma eRelWP_indicator_eqRel_le
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    eRelWP oa ob (RelPost.indicator (EqRel α)) ≤
      ∑' a, min (Pr[= a | evalDist oa]) (Pr[= a | evalDist ob]) := by
  letI : DecidableEq α := Classical.decEq α
  unfold eRelWP
  refine iSup_le fun c => ?_
  calc ∑' z, Pr[= z | c.1] * RelPost.indicator (EqRel α) z.1 z.2
      = ∑' z : α × α, if z.1 = z.2 then Pr[= z | c.1] else 0 := by
        congr 1; ext ⟨a, b⟩; simp [RelPost.indicator, EqRel]
    _ = ∑' a, Pr[= (a, a) | c.1] := by
        rw [show (fun z : α × α => if z.1 = z.2 then Pr[= z | c.1] else 0) =
            (fun z : α × α => if z.1 = z.2 then Pr[= (z.1, z.2) | c.1] else 0)
            from by ext ⟨a, b⟩; rfl,
          ENNReal.tsum_prod']
        congr 1; ext a
        rw [tsum_eq_single a (fun b hb => if_neg (Ne.symm hb))]
        simp
    _ ≤ ∑' a, min (Pr[= a | evalDist oa]) (Pr[= a | evalDist ob]) :=
        ENNReal.tsum_le_tsum fun a => probOutput_diag_le_min_marginals c a

private lemma min_add_tsub (a b : ℝ≥0∞) : min a b + (a - b) = a := by
  rcases le_total a b with hab | hab
  · simp [min_eq_left hab, tsub_eq_zero_of_le hab]
  · rw [min_eq_right hab, add_comm]
    exact tsub_add_cancel_of_le hab

private lemma tsum_min_add_etvDist_eq_one
    {p q : PMF (Option α)} (hp : p none = 0) (hq : q none = 0) :
    ∑' a, min (p (some a)) (q (some a)) + p.etvDist q = 1 := by
  set S := ∑' a, min (p (some a)) (q (some a))
  have hsum_p : ∑' a, p (some a) = 1 := by
    have := p.tsum_coe; rw [tsum_option _ ENNReal.summable, hp, zero_add] at this; exact this
  have hsum_q : ∑' a, q (some a) = 1 := by
    have := q.tsum_coe; rw [tsum_option _ ENNReal.summable, hq, zero_add] at this; exact this
  have hS_le : S ≤ 1 := hsum_p ▸ ENNReal.tsum_le_tsum fun a => min_le_left _ _
  have h1 : S + ∑' a, (p (some a) - q (some a)) = 1 := by
    rw [← ENNReal.tsum_add, ← hsum_p]
    exact tsum_congr fun a => min_add_tsub (p (some a)) (q (some a))
  have h2 : S + ∑' a, (q (some a) - p (some a)) = 1 := by
    rw [← ENNReal.tsum_add, ← hsum_q]
    exact tsum_congr fun a => by rw [min_comm]; exact min_add_tsub (q (some a)) (p (some a))
  have hS_ne_top : S ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hS_le
  have htsub1 : ∑' a, (p (some a) - q (some a)) = 1 - S :=
    ENNReal.eq_sub_of_add_eq hS_ne_top (by rwa [add_comm] at h1)
  have htsub2 : ∑' a, (q (some a) - p (some a)) = 1 - S :=
    ENNReal.eq_sub_of_add_eq hS_ne_top (by rwa [add_comm] at h2)
  have habsdiff_sum : ∑' a, ENNReal.absDiff (p (some a)) (q (some a)) = 2 * (1 - S) := by
    rw [show (fun a => ENNReal.absDiff (p (some a)) (q (some a))) =
        (fun a => (p (some a) - q (some a)) + (q (some a) - p (some a)))
        from funext fun _ => rfl,
      ENNReal.tsum_add, htsub1, htsub2, two_mul]
  rw [PMF.etvDist, show ∑' x, ENNReal.absDiff (p x) (q x) =
      ∑' a, ENNReal.absDiff (p (some a)) (q (some a)) from by
    rw [tsum_option _ ENNReal.summable, hp, hq, ENNReal.absDiff_self, zero_add],
    habsdiff_sum]
  rw [show (2 : ℝ≥0∞) * (1 - S) / 2 = 1 - S from by
    rw [mul_comm]; exact ENNReal.mul_div_cancel_right two_ne_zero ofNat_ne_top]
  exact add_tsub_cancel_of_le hS_le

private lemma tsum_min_eq_one_sub_etvDist
    {p q : PMF (Option α)} (hp : p none = 0) (hq : q none = 0) :
    ∑' a, min (p (some a)) (q (some a)) = 1 - p.etvDist q := by
  have h := tsum_min_add_etvDist_eq_one hp hq
  exact ENNReal.eq_sub_of_add_eq (PMF.etvDist_ne_top p q) h

private lemma tsum_min_probOutput_eq_one_sub_etvDist
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    ∑' a, min (Pr[= a | evalDist oa]) (Pr[= a | evalDist ob]) =
      1 - (evalDist oa).toPMF.etvDist (evalDist ob).toPMF := by
  simp_rw [show ∀ a, min (Pr[= a | evalDist oa]) (Pr[= a | evalDist ob]) =
      min ((evalDist oa).toPMF (some a)) ((evalDist ob).toPMF (some a))
      from fun a => by simp [probOutput_def, SPMF.apply_eq_toPMF_some]]
  exact tsum_min_eq_one_sub_etvDist
    (probFailure_eq_zero (mx := oa))
    (probFailure_eq_zero (mx := ob))

private lemma tsum_min_le_eRelWP
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    ∑' a, min (Pr[= a | evalDist oa]) (Pr[= a | evalDist ob]) ≤
      eRelWP oa ob (RelPost.indicator (EqRel α)) := by
  letI : DecidableEq α := Classical.decEq α
  set pa := evalDist oa; set pb := evalDist ob
  set P := fun a => Pr[= a | pa]; set Q := fun a => Pr[= a | pb]
  set rP := fun a => P a - min (P a) (Q a)
  set rQ := fun a => Q a - min (Q a) (P a)
  set δ := ∑' a, rP a
  have hP_sum : ∑' a, P a = 1 := HasEvalPMF.tsum_probOutput_eq_one oa
  have hQ_sum : ∑' a, Q a = 1 := HasEvalPMF.tsum_probOutput_eq_one ob
  have hδ_ne_top : δ ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (hP_sum ▸ ENNReal.tsum_le_tsum fun a => tsub_le_self)
  have hδ_eq_rQ : ∑' a, rQ a = δ := by
    have hS_ne_top : (∑' a, min (P a) (Q a)) ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top (hP_sum ▸ ENNReal.tsum_le_tsum fun a => min_le_left _ _)
    have h1 : ∑' a, min (P a) (Q a) + δ = 1 := by
      rw [← ENNReal.tsum_add, ← hP_sum]
      exact tsum_congr fun a =>
        show min (P a) (Q a) + (P a - min (P a) (Q a)) = P a from
          add_tsub_cancel_of_le (min_le_left _ _)
    have h2 : ∑' a, min (P a) (Q a) + ∑' a, rQ a = 1 := by
      rw [← ENNReal.tsum_add, ← hQ_sum]
      exact tsum_congr fun a =>
        show min (P a) (Q a) + (Q a - min (Q a) (P a)) = Q a from by
          rw [min_comm]; exact add_tsub_cancel_of_le (min_le_left _ _)
    exact ((ENNReal.add_right_inj hS_ne_top).mp (h1.trans h2.symm)).symm
  have hmul_δ : ∀ a, rP a * (δ * δ⁻¹) = rP a := by
    intro a
    rcases eq_or_ne δ 0 with hδ0 | hδ0
    · have : rP a = 0 := le_antisymm (hδ0 ▸ ENNReal.le_tsum a) bot_le
      simp [this, hδ0]
    · rw [ENNReal.mul_inv_cancel hδ0 hδ_ne_top, mul_one]
  set cf : Option (α × α) → ℝ≥0∞ := fun
    | none => 0
    | some (a, b) => (if a = b then min (P a) (Q a) else 0) + rP a * rQ b * δ⁻¹
  have hfst_sum : ∀ a, ∑' b, cf (some (a, b)) = P a := by
    intro a
    change ∑' b, ((if a = b then min (P a) (Q a) else 0) + rP a * rQ b * δ⁻¹) = P a
    rw [ENNReal.tsum_add]
    rw [tsum_eq_single a (fun b hb => if_neg (Ne.symm hb))]
    simp only [ite_true]
    simp_rw [show ∀ b, rP a * rQ b * δ⁻¹ = (rP a * δ⁻¹) * rQ b
        from fun b => mul_right_comm _ _ _]
    rw [ENNReal.tsum_mul_left, hδ_eq_rQ, mul_assoc, mul_comm δ⁻¹ δ, hmul_δ]
    change min (P a) (Q a) + (P a - min (P a) (Q a)) = P a
    exact add_tsub_cancel_of_le (min_le_left _ _)
  have hsnd_sum : ∀ b, ∑' a, cf (some (a, b)) = Q b := by
    intro b
    change ∑' a, ((if a = b then min (P a) (Q a) else 0) + rP a * rQ b * δ⁻¹) = Q b
    rw [ENNReal.tsum_add]
    conv_lhs => arg 1; rw [show
      (fun a => if a = b then min (P a) (Q a) else (0 : ℝ≥0∞)) =
        (fun a => if a = b then min (Q b) (P b) else 0) from by
          ext a
          split <;> simp_all [min_comm]]
    rw [tsum_eq_single b (fun a ha => if_neg ha)]
    simp only [ite_true]
    have htsum_rQ : ∑' a, rP a * rQ b * δ⁻¹ = rQ b := by
      simp_rw [show ∀ a, rP a * rQ b * δ⁻¹ = rQ b * δ⁻¹ * rP a
          from fun a => by rw [mul_assoc, mul_comm]]
      rw [ENNReal.tsum_mul_left]
      rcases eq_or_ne δ 0 with hδ0 | hδ0
      · have hrQ0 : rQ b = 0 :=
          le_antisymm (hδ0 ▸ hδ_eq_rQ ▸ ENNReal.le_tsum b) bot_le
        simp only [hrQ0, zero_mul]
      · rw [mul_assoc, ENNReal.inv_mul_cancel hδ0 hδ_ne_top, mul_one]
    rw [htsum_rQ]
    change min (Q b) (P b) + (Q b - min (Q b) (P b)) = Q b
    exact add_tsub_cancel_of_le (min_le_left _ _)
  have hcf_sum : ∑' x, cf x = 1 := by
    rw [tsum_option _ ENNReal.summable, show cf none = 0 from rfl, zero_add]
    rw [ENNReal.tsum_prod']
    rw [show ∑' a, ∑' b, cf (some (a, b)) = ∑' a, P a from
      tsum_congr fun a => hfst_sum a]
    exact hP_sum
  let c_pmf : PMF (Option (α × α)) := ⟨cf, hcf_sum ▸ ENNReal.summable.hasSum⟩
  let c_spmf : SPMF (α × α) := c_pmf
  have hite_tsum : ∀ {β : Type} (P : Prop) [Decidable P] (f : β → ℝ≥0∞),
      ∑' b, (if P then f b else 0) = if P then ∑' b, f b else 0 := by
    intro β P _ f; split <;> simp_all
  have hcpl_fst : Prod.fst <$> c_spmf = pa := by
    apply SPMF.ext; intro a
    rw [show (Prod.fst <$> c_spmf) a = Pr[= a | Prod.fst <$> c_spmf] from rfl,
      probOutput_map_eq_tsum_ite c_spmf Prod.fst a]
    change ∑' z : α × α, (if a = z.1 then cf (some z) else 0) = P a
    rw [ENNReal.tsum_prod']; dsimp only [Prod.fst]
    rw [tsum_congr fun a₁ => hite_tsum (a = a₁) (fun b => cf (some (a₁, b)))]
    rw [tsum_eq_single a (fun a' (ha' : a' ≠ a) => if_neg (Ne.symm ha'))]
    rw [if_pos rfl, hfst_sum]
  have hcpl_snd : Prod.snd <$> c_spmf = pb := by
    apply SPMF.ext; intro b
    rw [show (Prod.snd <$> c_spmf) b = Pr[= b | Prod.snd <$> c_spmf] from rfl,
      probOutput_map_eq_tsum_ite c_spmf Prod.snd b]
    change ∑' z : α × α, (if b = z.2 then cf (some z) else 0) = Q b
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]; dsimp only [Prod.snd]
    rw [tsum_congr fun b₁ => hite_tsum (b = b₁) (fun a => cf (some (a, b₁)))]
    rw [tsum_eq_single b (fun b' (hb' : b' ≠ b) => if_neg (Ne.symm hb'))]
    rw [if_pos rfl, hsnd_sum]
  let c : SPMF.Coupling pa pb :=
    ⟨c_spmf, ⟨hcpl_fst, hcpl_snd⟩⟩
  have hobj_eq : ∑' z : α × α, Pr[= z | c.1] * RelPost.indicator (EqRel α) z.1 z.2 =
      ∑' a, cf (some (a, a)) := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun a => ?_
    rw [tsum_eq_single a fun b hb => ?_]
    · simp only [RelPost.indicator, EqRel, ite_true, mul_one, SPMF.probOutput_eq_apply]; rfl
    · simp [RelPost.indicator, EqRel, Ne.symm hb]
  calc ∑' a, min (P a) (Q a)
      ≤ ∑' a, cf (some (a, a)) := ENNReal.tsum_le_tsum fun a => by
        change min (P a) (Q a) ≤ (if a = a then min (P a) (Q a) else 0) + _
        simp
    _ = ∑' z : α × α, Pr[= z | c.1] * RelPost.indicator (EqRel α) z.1 z.2 :=
        hobj_eq.symm
    _ ≤ eRelWP oa ob (RelPost.indicator (EqRel α)) :=
        le_iSup (fun c' : SPMF.Coupling pa pb =>
          ∑' z, Pr[= z | c'.1] * RelPost.indicator (EqRel α) z.1 z.2) c

/-! ## Statistical distance via eRHL -/

/-- Statistical distance as a complement of eRHL value with equality indicator.
Uses `SPMF.tvDist` directly to handle cross-spec comparison. -/
theorem spmf_tvDist_eq_one_sub_eRelWP_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    SPMF.tvDist (evalDist oa) (evalDist ob) =
      (1 - eRelWP oa ob (RelPost.indicator (EqRel α))).toReal := by
  set p := (evalDist oa).toPMF
  set q := (evalDist ob).toPMF
  have htmin := tsum_min_probOutput_eq_one_sub_etvDist (oa := oa) (ob := ob)
  have hle : eRelWP oa ob (RelPost.indicator (EqRel α)) ≤ 1 - p.etvDist q :=
    htmin ▸ eRelWP_indicator_eqRel_le
  have hge : 1 - p.etvDist q ≤ eRelWP oa ob (RelPost.indicator (EqRel α)) :=
    htmin ▸ tsum_min_le_eRelWP
  have heq : eRelWP oa ob (RelPost.indicator (EqRel α)) =
      1 - (evalDist oa).toPMF.etvDist (evalDist ob).toPMF := le_antisymm hle hge
  simp only [heq, SPMF.tvDist, PMF.tvDist,
    ENNReal.sub_sub_cancel one_ne_top (PMF.etvDist_le_one _ _)]

/-- Same-spec version using the `tvDist` notation. -/
theorem tvDist_eq_one_sub_eRelWP_eqRel
    {oa ob : OracleComp spec₁ α} :
    tvDist oa ob = (1 - eRelWP (spec₂ := spec₁) oa ob
      (RelPost.indicator (EqRel α))).toReal := by
  simpa [tvDist] using
    (spmf_tvDist_eq_one_sub_eRelWP_eqRel
      (spec₁ := spec₁) (spec₂ := spec₁) (oa := oa) (ob := ob))

/-- Game equivalence from pRHL equality coupling. -/
theorem gameEquiv_of_relTriple'_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple' oa ob (EqRel α)) :
    evalDist oa = evalDist ob :=
  evalDist_eq_of_relTriple_eqRel (relTriple'_iff_relTriple.mp h)

end OracleComp.ProgramLogic.Relational
