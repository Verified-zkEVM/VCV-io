/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Advantage
import VCVio.HeapSSP.Composition

/-!
# HeapSSP: Distributional Equivalence

`Package.DistEquiv G₀ G₁` (notation `G₀ ≡ᵈ G₁`) says that two probability-only
heap-packages produce identical output distributions against *every*
adversary, on every output type. The heap-package counterpart of
`VCVio.SSP.DistEquiv`.

The identifier sets `Ident₀, Ident₁` of the two games may be unrelated; only
their behaviour against adversaries matters. This is exactly the
"behavioural equivalence" of state-separating proofs, ported to the heap
framework.

## API surface

* **Relation laws**: `refl`, `symm`, `trans`, plus a `Trans` instance for
  `calc` blocks and a named `Equivalence` witness when the identifier set
  is fixed.
* **Constructors**:
  * `of_run_evalDist`: from a per-adversary `evalDist` equality (the
    unfolded definition).
  * `of_step`: same identifier set, agree per-query under `evalDist`. The
    lemma version of `Package.simulateQ_StateT_evalDist_congr` from
    `VCVio.HeapSSP.Advantage`.
  * `of_step_bij`: heap-bijected identifier sets, agree per-query under
    `evalDist` modulo the bijection. The lemma version of
    `Package.simulateQ_StateT_evalDist_congr_of_bij`. Useful for
    `Heap.split`-based reshapes inside `par`-composed packages.
* **Bridge to `Package.advantage`**: `advantage_left`, `advantage_right`,
  `advantage_zero`. A `≡ᵈ`-hop on either side preserves the Boolean
  distinguishing advantage.
* **Bridge to `runProb`**: `runProb_evalDist_eq`, the inverse of
  `of_run_evalDist`.

## Composition

* **`link` congruence in the inner argument**: `link_inner_congr` swaps the
  inner game of a linked composition along a `≡ᵈ`-hop, leveraging
  `Package.run_link_eq_run_shiftLeft`. The bound (perfect) case is exactly
  the SSProve "ε = 0 in the inner game" reduction.
* The outer-side congruence and `par_congr` are not yet in this file: the
  former requires a notion of equivalence for *open* packages (per-handler
  under `evalDist`), and the latter requires parallel-composition
  structural reductions specific to the heap framework. Both are scheduled
  as follow-ups.
-/

universe uₘ uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.HeapSSP

namespace Package

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- Two probability-only heap-packages are *distributionally equivalent* if
they produce the same output distribution against every adversary, on every
output type.

Equivalent characterisations:
* The Boolean distinguishing advantage `G₀.advantage G₁ A` is zero on every
  Boolean-valued adversary `A` (`DistEquiv.advantage_zero`).
* For every `α` and every adversary `A : OracleComp E α`,
  `evalDist (G₀.runProb A) = evalDist (G₁.runProb A)` (the literal
  definition).

The identifier sets `Ident₀, Ident₁` of the two games are independent: only
the export interface and the resulting output distribution matter from an
adversary's point of view. -/
def DistEquiv {Ident₀ Ident₁ : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₁]
    (G₀ : Package unifSpec E Ident₀) (G₁ : Package unifSpec E Ident₁) :
    Prop :=
  ∀ {α : Type} (A : OracleComp E α),
    evalDist (G₀.runProb A) = evalDist (G₁.runProb A)

@[inherit_doc DistEquiv]
scoped infix:50 " ≡ᵈ " => Package.DistEquiv

namespace DistEquiv

variable {Ident Ident₀ Ident₁ Ident₂ : Type}
  [CellSpec.{0, 0} Ident] [CellSpec.{0, 0} Ident₀]
  [CellSpec.{0, 0} Ident₁] [CellSpec.{0, 0} Ident₂]

/-! ### Relation laws -/

@[refl]
protected theorem refl (G : Package unifSpec E Ident) : G ≡ᵈ G :=
  fun _ => rfl

@[symm]
protected theorem symm
    {G₀ : Package unifSpec E Ident₀} {G₁ : Package unifSpec E Ident₁}
    (h : G₀ ≡ᵈ G₁) : G₁ ≡ᵈ G₀ :=
  fun A => (h A).symm

@[trans]
protected theorem trans
    {G₀ : Package unifSpec E Ident₀} {G₁ : Package unifSpec E Ident₁}
    {G₂ : Package unifSpec E Ident₂}
    (h₀₁ : G₀ ≡ᵈ G₁) (h₁₂ : G₁ ≡ᵈ G₂) : G₀ ≡ᵈ G₂ :=
  fun A => (h₀₁ A).trans (h₁₂ A)

instance trans_instance :
    @Trans (Package unifSpec E Ident₀) (Package unifSpec E Ident₁)
      (Package unifSpec E Ident₂) DistEquiv DistEquiv DistEquiv where
  trans := DistEquiv.trans

/-- When the identifier set is fixed, `≡ᵈ` is an `Equivalence`. -/
theorem _root_.VCVio.HeapSSP.Package.equivalence_distEquiv
    (E : OracleSpec.{uₑ, 0} ιₑ) (Ident : Type) [CellSpec.{0, 0} Ident] :
    Equivalence
      (DistEquiv (E := E) (Ident₀ := Ident) (Ident₁ := Ident)) where
  refl := DistEquiv.refl
  symm := DistEquiv.symm
  trans := DistEquiv.trans

/-! ### Constructors -/

/-- Build a `DistEquiv` from the literal per-adversary `evalDist` equality.
The unfolded definition, exposed for clients that already have the
distribution equality in hand. -/
theorem of_run_evalDist
    {G₀ : Package unifSpec E Ident₀} {G₁ : Package unifSpec E Ident₁}
    (h : ∀ {α : Type} (A : OracleComp E α),
        evalDist (G₀.runProb A) = evalDist (G₁.runProb A)) :
    G₀ ≡ᵈ G₁ := h

/-- Recover the per-adversary `evalDist` equality from a `DistEquiv`
witness. The inverse of `of_run_evalDist`. -/
theorem runProb_evalDist_eq
    {G₀ : Package unifSpec E Ident₀} {G₁ : Package unifSpec E Ident₁}
    (h : G₀ ≡ᵈ G₁) {α : Type} (A : OracleComp E α) :
    evalDist (G₀.runProb A) = evalDist (G₁.runProb A) := h A

/-- Build a `DistEquiv` from a per-adversary *propositional* equality at the
`runProb` level. -/
theorem of_run_eq
    {G₀ : Package unifSpec E Ident₀} {G₁ : Package unifSpec E Ident₁}
    (h : ∀ {α : Type} (A : OracleComp E α), G₀.runProb A = G₁.runProb A) :
    G₀ ≡ᵈ G₁ :=
  fun A => by rw [h A]

/-- **Step constructor (same identifier set).** Two probability-only
heap-packages with identical identifier set are distributionally equivalent
if their inits agree under `evalDist` and their per-query handlers agree
under `evalDist` on every heap.

The lemma form of `Package.simulateQ_StateT_evalDist_congr` from
`VCVio.HeapSSP.Advantage`, lifted to the package level: the per-handler
hypothesis discharges the simulation step, and the init hypothesis
discharges the setup step. -/
theorem of_step {G₀ G₁ : Package unifSpec E Ident}
    (h_init : evalDist G₀.init = evalDist G₁.init)
    (h_impl : ∀ (q : E.Domain) (h : Heap Ident),
        evalDist ((G₀.impl q).run h) = evalDist ((G₁.impl q).run h)) :
    G₀ ≡ᵈ G₁ := by
  intro α A
  change evalDist (G₀.run A) = evalDist (G₁.run A)
  unfold Package.run
  rw [evalDist_bind, evalDist_bind, h_init]
  refine bind_congr fun s₀ => ?_
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  exact simulateQ_StateT_evalDist_congr h_impl A s₀

/-- **Step constructor (under heap bijection).** Two probability-only
heap-packages with isomorphic *heap types* `Heap Ident₀ ≃ Heap Ident₁` are
distributionally equivalent if their inits agree under `evalDist` modulo
the bijection (RHS init is mapped through `φ.symm`) and their per-query
handlers agree under `evalDist` modulo the bijection (RHS handler output
is mapped through `Prod.map id φ.symm`).

The lemma form of `Package.simulateQ_StateT_evalDist_congr_of_bij` from
`VCVio.HeapSSP.Advantage`, lifted to the package level. The bijection is
on the *underlying state* (here `Heap Ident`) rather than on identifier
sets directly, so it accommodates the canonical
`Heap.split : Heap (α ⊕ β) ≃ Heap α × Heap β` reshape used by
`par`-composed packages. -/
theorem of_step_bij
    (G₀ : Package unifSpec E Ident₀) (G₁ : Package unifSpec E Ident₁)
    (φ : Heap Ident₀ ≃ Heap Ident₁)
    (h_init : evalDist G₀.init = evalDist (φ.symm <$> G₁.init))
    (h_impl : ∀ (q : E.Domain) (h : Heap Ident₀),
        evalDist ((G₀.impl q).run h) =
          evalDist (Prod.map id φ.symm <$> (G₁.impl q).run (φ h))) :
    G₀ ≡ᵈ G₁ := by
  intro α A
  change evalDist (G₀.run A) = evalDist (G₁.run A)
  unfold Package.run
  rw [evalDist_bind, evalDist_bind, h_init, evalDist_map]
  rw [bind_map_left]
  refine bind_congr fun s₁ => ?_
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  have hbij :=
    simulateQ_StateT_evalDist_congr_of_bij G₀.impl G₁.impl φ h_impl A
      (φ.symm s₁)
  rw [Equiv.apply_symm_apply] at hbij
  rw [hbij, evalDist_map]
  simp only [Functor.map_map, Prod.map_fst, id_eq]

/-! ### Bridge to `Package.advantage` -/

/-- A distributional equivalence on the LEFT side preserves the Boolean
distinguishing advantage. -/
theorem advantage_left
    {G₀ : Package unifSpec E Ident₀} {G₀' : Package unifSpec E Ident}
    (h : G₀ ≡ᵈ G₀')
    (G₁ : Package unifSpec E Ident₁) (A : OracleComp E Bool) :
    G₀.advantage G₁ A = G₀'.advantage G₁ A :=
  advantage_eq_of_evalDist_runProb_eq (h A)

/-- A distributional equivalence on the RIGHT side preserves the Boolean
distinguishing advantage. -/
theorem advantage_right
    (G₀ : Package unifSpec E Ident₀)
    {G₁ : Package unifSpec E Ident₁} {G₁' : Package unifSpec E Ident}
    (h : G₁ ≡ᵈ G₁') (A : OracleComp E Bool) :
    G₀.advantage G₁ A = G₀.advantage G₁' A :=
  advantage_eq_of_evalDist_runProb_eq_right (h A)

/-- Distributionally equivalent heap-packages have zero distinguishing
advantage. -/
theorem advantage_zero
    {G₀ : Package unifSpec E Ident₀} {G₁ : Package unifSpec E Ident₁}
    (h : G₀ ≡ᵈ G₁) (A : OracleComp E Bool) :
    G₀.advantage G₁ A = 0 := by
  rw [advantage_left h G₁ A, advantage_self]

/-! ### Compositional congruences (`link`) -/

section LinkCongr

variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}
variable {Ident_P : Type} [CellSpec.{0, 0} Ident_P]

/-- **Inner-game congruence for `link`.** Swapping the inner game of a
linked composition along a `≡ᵈ`-hop preserves distributional equivalence:
the outer reduction `P` is absorbed into the shifted adversary
`P.shiftLeft A`, and the equivalence on the inner game closes the proof.

The SSP "replace the inner game" rule, the program-level counterpart of
`Package.advantage_link_left_eq_advantage_shiftLeft` in
`VCVio.HeapSSP.Hybrid`. -/
theorem link_inner_congr (P : Package M E Ident_P)
    {Q₀ : Package unifSpec M Ident₀} {Q₁ : Package unifSpec M Ident₁}
    (h : Q₀ ≡ᵈ Q₁) :
    P.link Q₀ ≡ᵈ P.link Q₁ := by
  intro α A
  change evalDist ((P.link Q₀).run A) = evalDist ((P.link Q₁).run A)
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]
  exact h (P.shiftLeft A)

end LinkCongr

end DistEquiv

end Package

end VCVio.HeapSSP
