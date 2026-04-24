/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Lens.Basic

/-!
# Cartesian Lenses Between Polynomial Functors

A `Lens P Q` between polynomial functors carries a forward map on positions
(`toFunA : P.A → Q.A`) and, for each position `a : P.A`, a backward map on
directions (`toFunB a : Q.B (toFunA a) → P.B a`). We say the lens is
**cartesian** when every backward map `toFunB a` is a bijection.

In the language of the fibration `Poly → Set` that sends a polynomial
functor to its set of positions, cartesian lenses are exactly the
cartesian morphisms: the type-square underlying each fiber is a pullback.
A cartesian lens is a *fiberwise isomorphism* over an arbitrary forward
map on positions.

The two extremes of the orthogonal factorization system on `Poly` are
captured separately:

* a **vertical** lens has `toFunA = id` (only the directions move);
* a **cartesian** lens has each `toFunB a` a bijection (only the positions
  move freely; each fiber is rigid).

A `PFunctor.Lens.Equiv` (a categorical isomorphism in the lens category)
is the intersection of the two: `toFunA` is a bijection AND every
`toFunB a` is a bijection. Thus *every* `Equiv` is cartesian, but a
cartesian lens whose position map is not a bijection (e.g.
`Lens.inl : Lens P (P + Q)`) is not an `Equiv`.

The downstream consumer of this file is `LawfulSubSpec` in
`VCVio/OracleComp/Coercions/SubSpec.lean`: a `LawfulSubSpec` is by
definition the predicate "the underlying
`Lens spec.toPFunctor superSpec.toPFunctor` is cartesian", which is the
exact condition needed to pull the uniform distribution on
`superSpec.Range` back through a sub-spec embedding without distortion.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A lens `l : Lens P Q` is **cartesian** when every backward fiber
`l.toFunB a : Q.B (l.toFunA a) → P.B a` is a bijection. Equivalently,
`l` is a cartesian morphism in the fibration `Poly → Set` of polynomial
functors over their position sets. -/
def IsCartesian (l : Lens P Q) : Prop :=
  ∀ a, Function.Bijective (l.toFunB a)

namespace IsCartesian

@[simp]
theorem id_lens (P : PFunctor.{uA, uB}) : (Lens.id P).IsCartesian := fun _ =>
  Function.bijective_id

theorem comp {l₁ : Lens Q R} {l₂ : Lens P Q}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ∘ₗ l₂).IsCartesian := fun a =>
  (h₂ a).comp (h₁ (l₂.toFunA a))

end IsCartesian

/-! ## Cartesianness of canonical lens constructors

Most "embedding-shaped" lenses produced by the lens algebra are cartesian.
We collect the witnesses here so that downstream classes (notably
`LawfulSubSpec`) can be discharged uniformly. -/

namespace IsCartesian

theorem inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inl : Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q)).IsCartesian := fun _ =>
  Function.bijective_id

theorem inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inr : Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q)).IsCartesian := fun _ =>
  Function.bijective_id

theorem sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ⊎ₗ l₂).IsCartesian
  | Sum.inl a => h₁ a
  | Sum.inr a => h₂ a

theorem sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB₃}} {l₁ : Lens P R} {l₂ : Lens Q R}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (Lens.sumPair l₁ l₂).IsCartesian
  | Sum.inl a => h₁ a
  | Sum.inr a => h₂ a

theorem sigmaMap {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) (G i)} (hl : ∀ i, (l i).IsCartesian) :
    (Lens.sigmaMap l).IsCartesian
  | ⟨i, fa⟩ => hl i fa

theorem sigmaExists {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) R} (hl : ∀ i, (l i).IsCartesian) :
    (Lens.sigmaExists l).IsCartesian
  | ⟨i, fa⟩ => hl i fa

end IsCartesian

/-! ## Sigma injection

The natural inclusion of the `j`-th summand into a `sigma`: the unique
lens whose forward action picks the `j`-th tag and whose backward action
is the identity on directions. This is the `Lens` whose corresponding
`MonadLift` underlies `OracleSpec.subSpec_sigma`. -/

/-- Lens injection `Lens (F j) (sigma F)` for a fixed index `j : I`. -/
def sigmaInj {I : Type v} {F : I → PFunctor.{uA, uB}} (j : I) :
    Lens (F j) (sigma F) :=
  (fun fa => ⟨j, fa⟩) ⇆ (fun _ d => d)

namespace IsCartesian

theorem sigmaInj {I : Type v} {F : I → PFunctor.{uA, uB}} (j : I) :
    (Lens.sigmaInj (F := F) j).IsCartesian := fun _ =>
  Function.bijective_id

end IsCartesian

end Lens

end PFunctor
