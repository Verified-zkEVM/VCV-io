import ToMathlib.ProbabilityTheory.Coupling
import VCVio.EvalDist.Defs.Instances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist

/-!
# Relational program-logic baseline

This file provides a coupling-centered baseline (`RelTriple`) for compositional
relational reasoning.
-/

open ENNReal

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

/-- Relational postconditions over two output spaces. -/
abbrev RelPost (α : Type) (β : Type) := α → β → Prop

/-- Equality relation helper for same-type outputs. -/
def EqRel (α : Type) : RelPost α α := fun x y => x = y

/-- Existence of an `SPMF` coupling witness between two computations. -/
def HasCoupling (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) : Prop :=
  Nonempty (_root_.SPMF.Coupling (evalDist oa) (evalDist ob))

/-- Coupling-based relational triple with support-level relational guarantee. -/
def RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  ∃ c : _root_.SPMF.Coupling (evalDist oa) (evalDist ob),
    ∀ z ∈ support c.1, R z.1 z.2

/-- Any coupling-based relational triple yields a coupling witness. -/
lemma hasCoupling_of_relTriple {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (h : RelTriple oa ob R) : HasCoupling oa ob := by
  rcases h with ⟨c, _⟩
  exact ⟨c⟩

/-- Reflexivity rule for coupling-based relational triples. -/
lemma relTriple_refl (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) := by
  refine ⟨_root_.SPMF.Coupling.refl (evalDist oa), ?_⟩
  intro z hz
  rcases (mem_support_bind_iff (evalDist oa) (fun a => (pure (a, a) : SPMF (α × α))) z).1 hz with
    ⟨a, _, hz'⟩
  have hzEq : z = (a, a) := by
    simpa [support_pure, Set.mem_singleton_iff] using hz'
  simp [EqRel, hzEq]

/-- Postcondition monotonicity for coupling-based relational triples. -/
lemma relTriple_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R R' : RelPost α β}
    (h : RelTriple oa ob R)
    (hpost : ∀ ⦃x y⦄, R x y → R' x y) :
    RelTriple oa ob R' := by
  rcases h with ⟨c, hc⟩
  exact ⟨c, fun z hz => hpost (hc z hz)⟩

/-- Bind composition rule for coupling-based relational triples. -/
lemma relTriple_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R)
    (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S := by
  rcases hxy with ⟨c, hcR⟩
  classical
  let d : α → β → SPMF (γ × δ) := fun a b =>
    if hR : R a b then (Classical.choose (hfg a b hR)).1 else failure
  have hd :
      ∀ a b, c.1.1 (some (a, b)) ≠ 0 →
        _root_.SPMF.IsCoupling (d a b) (evalDist (fa a)) (evalDist (fb b)) := by
    intro a b hmass
    have hmass' : c.1 (a, b) ≠ 0 := by
      simpa [SPMF.apply_eq_toPMF_some] using hmass
    have hsupp : (a, b) ∈ support c.1 := (mem_support_iff c.1 (a, b)).2 hmass'
    have hR : R a b := hcR (a, b) hsupp
    simpa [d, hR] using (Classical.choose (hfg a b hR)).2
  have hbind :
      _root_.SPMF.IsCoupling
        (c.1 >>= fun p => d p.1 p.2)
        (evalDist oa >>= fun a => evalDist (fa a))
        (evalDist ob >>= fun b => evalDist (fb b)) :=
    _root_.SPMF.IsCoupling.bind c d hd
  refine ⟨⟨c.1 >>= fun p => d p.1 p.2, ?_⟩, ?_⟩
  · simpa [evalDist_bind] using hbind
  · intro z hz
    rcases (mem_support_bind_iff c.1 (fun p => d p.1 p.2) z).1 hz with ⟨ab, hab, hz'⟩
    have hR : R ab.1 ab.2 := hcR ab hab
    have hsub : RelTriple (fa ab.1) (fb ab.2) S := hfg ab.1 ab.2 hR
    exact Classical.choose_spec hsub z (by simpa [d, hR] using hz')

end OracleComp.ProgramLogic.Relational
