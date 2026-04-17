/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.Package
import VCVio.OracleComp.Coercions.Add

/-!
# State-Separating Proofs: Composition

This file defines the two basic composition operators on `Package`s:

* `Package.link` — sequential composition. Given an outer package importing `M` and exporting
  `E`, and an inner package importing `I` and exporting `M`, produce a single package importing
  `I` and exporting `E`, with state `σ₁ × σ₂`.
* `Package.par` — parallel composition. Given two packages with disjoint export and import
  interfaces, combine them into a single package on the disjoint sums `I₁ + I₂` and `E₁ + E₂`,
  with state `σ₁ × σ₂`.

These correspond to SSProve's `link` and `par`. Disjointness of the two state factors is
structural: each side's handler can only modify its own factor, so non-interference is a
type-level fact rather than a separation predicate that needs to be proved.

Equational theory (associativity, commutativity up to `Sum.swap`, identity, interchange) is
the subject of follow-up files. The basic shape lemmas (`init_link`, `init_par`, `run_pure`)
are immediate from the definitions.
-/

universe u v w

open OracleSpec OracleComp

namespace VCVio.SSP

namespace Package

variable {ιᵢ ιₘ ιₑ : Type u}
  {I : OracleSpec.{u, v} ιᵢ} {M : OracleSpec.{u, v} ιₘ} {E : OracleSpec.{u, v} ιₑ}
  {σ₁ σ₂ : Type v}

/-- Sequential composition of two packages: `outer ∘ inner`.

The outer package exports `E` and imports `M`. The inner package exports `M` and imports `I`.
The composite exports `E` and imports `I`, with state `σ₁ × σ₂` (outer state on the left,
inner state on the right). Each export query of the composite runs the outer handler in
state `σ₁`, then re-interprets every import-query in `M` it issues by running the inner
handler in state `σ₂`. -/
@[simps init]
def link (outer : Package M E σ₁) (inner : Package I M σ₂) : Package I E (σ₁ × σ₂) where
  init := (outer.init, inner.init)
  impl t := StateT.mk fun (s₁, s₂) =>
    let outerStep : OracleComp M (E.Range t × σ₁) := (outer.impl t).run s₁
    let innerStep : OracleComp I ((E.Range t × σ₁) × σ₂) :=
      (simulateQ inner.impl outerStep).run s₂
    (fun (p : (E.Range t × σ₁) × σ₂) => (p.1.1, (p.1.2, p.2))) <$> innerStep

/-- Linking with the identity package on the right is the original package, up to the canonical
state isomorphism `σ × PUnit ≃ σ`. Stated here as a definitional equality of impls is more
delicate than expected; we leave the precise statement to follow-up state-iso lemmas. -/
example (P : Package I E σ₁) : (P.link (Package.id I)).init = (P.init, PUnit.unit) := rfl

variable {ιᵢ₁ ιᵢ₂ ιₑ₁ ιₑ₂ : Type u}
  {I₁ : OracleSpec.{u, v} ιᵢ₁} {I₂ : OracleSpec.{u, v} ιᵢ₂}
  {E₁ : OracleSpec.{u, v} ιₑ₁} {E₂ : OracleSpec.{u, v} ιₑ₂}

/-- Parallel composition of two packages.

Given `p₁` exporting `E₁` and importing `I₁`, and `p₂` exporting `E₂` and importing `I₂`, the
parallel composite exports the disjoint sum `E₁ + E₂` and imports the disjoint sum `I₁ + I₂`.
Each side's handler is lifted along the obvious `OracleComp Iᵢ ⊂ₒ OracleComp (I₁ + I₂)` and
the resulting state is the product `σ₁ × σ₂`.

State separation is automatic: each side's handler can only access its own state component, so
modifications to the other side are behaviorally invisible. This is the structural-typing
counterpart of SSProve's `fseparate` side-condition.

We do not use `QueryImpl.prodStateT` here because of awkward universe unification through
`OracleSpec` sums; the body is the same up to the obvious lifts. -/
def par (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    Package (I₁ + I₂) (E₁ + E₂) (σ₁ × σ₂) where
  init := (p₁.init, p₂.init)
  impl
    | .inl t => StateT.mk fun (s₁, s₂) =>
        (Prod.map _root_.id (·, s₂)) <$> liftComp ((p₁.impl t).run s₁) (I₁ + I₂)
    | .inr t => StateT.mk fun (s₁, s₂) =>
        (Prod.map _root_.id (s₁, ·)) <$> liftComp ((p₂.impl t).run s₂) (I₁ + I₂)

@[simp]
lemma par_init (p₁ : Package I₁ E₁ σ₁) (p₂ : Package I₂ E₂ σ₂) :
    (p₁.par p₂).init = (p₁.init, p₂.init) := rfl

end Package

end VCVio.SSP
