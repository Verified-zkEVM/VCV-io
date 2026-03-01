import VCVio.OracleComp.EvalDist

/-!
# Relational program-logic baseline

Relational reasoning is intentionally kept lightweight for now while the unary quantitative
WP/triple API stabilizes.
-/

open ENNReal

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β : Type}

/-- Relational postconditions over two output spaces. -/
abbrev RelPost (α : Type) (β : Type) := α → β → Prop

/-- A minimal relational comparison: every related pair has pointwise probability domination. -/
def PointwiseDom (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  ∀ ⦃x y⦄, R x y → Pr[= x | oa] ≤ Pr[= y | ob]

/-- Equality relation helper for same-type outputs. -/
def EqRel (α : Type) : RelPost α α := fun x y => x = y

/-! A minimal relational triple skeleton (coupling-ready API surface). -/

/-- Minimal relational triple skeleton for two computations and a relational postcondition. -/
def RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : RelPost α β) : Prop :=
  PointwiseDom oa ob post

@[simp]
lemma pointwiseDom_refl (oa : OracleComp spec₁ α) :
    PointwiseDom (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) := by
  intro x y hxy
  subst hxy
  exact le_rfl

@[simp]
lemma relTriple_refl (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) :=
  pointwiseDom_refl (spec₁ := spec₁) oa

lemma pointwiseDom_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : RelPost α β}
    (h : PointwiseDom oa ob post) (hpost : ∀ ⦃x y⦄, post' x y → post x y) :
    PointwiseDom oa ob post' := by
  intro x y hxy
  exact h (hpost hxy)

lemma relTriple_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : RelPost α β}
    (h : RelTriple oa ob post) (hpost : ∀ ⦃x y⦄, post' x y → post x y) :
    RelTriple oa ob post' :=
  pointwiseDom_post_mono h hpost

end OracleComp.ProgramLogic.Relational
