/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Advantage
import VCVio.HeapSSP.Composition

/-!
# HeapSSP: Distributional Equivalence

`Package.DistEquiv G₀ G₁` (notation `G₀ ≡ᵈ G₁`) says that two heap-packages
sharing an export interface `E` and an import interface `I` produce
identical output distributions against every client computation, on every
output type in this probability layer.

The relation is polymorphic in the import: a `≡ᵈ`-hop is meaningful for any
`I : OracleSpec.{uᵢ, 0} ιᵢ` with `[I.Fintype]` `[I.Inhabited]`. The two key
instantiations are:

* **`I = unifSpec`** — the "probability-only" case. The bridge
  `advantage_zero` collapses a `≡ᵈ`-hop to a zero entry in
  `Package.advantage`.
* **`I = I₁ + I₂`** — the parallel-composition case. `par_congr` swaps
  one factor of a `Package.par` along a `≡ᵈ`-hop, leveraging the
  congruence directly *inside* the still-open import `I₁ + I₂`.

The identifier sets `Ident₀, Ident₁` of the two games may be unrelated; only
their behaviour against clients matters.

## API surface

* **Relation laws**: `refl`, `symm`, `trans`, plus a `Trans` instance for
  `calc` blocks and a named `Equivalence` witness when the identifier set
  is fixed.
* **Constructors**:
  * `of_run_evalDist`: from a per-client `evalDist` equality (the
    unfolded definition).
  * `of_run_eq`: from a per-client *propositional* equality at the
    `Package.run` level.
  * `of_step`: same identifier set, agree per-query under `evalDist`. The
    lemma version of `Package.simulateQ_StateT_evalDist_congr` from
    `VCVio.HeapSSP.Advantage`.
  * `of_step_bij`: heap-bijected identifier sets, agree per-query under
    `evalDist` modulo the bijection. The lemma version of
    `Package.simulateQ_StateT_evalDist_congr_of_bij`. Useful for
    `Heap.split`-based reshapes inside `par`-composed packages.
* **Bridge to `Package.advantage`** (specialised to `I = unifSpec`):
  `advantage_left`, `advantage_right`, `advantage_zero`. A `≡ᵈ`-hop on
  either side preserves the Boolean distinguishing advantage.
* **Bridge to `run`**: `run_evalDist_eq`, the inverse of
  `of_run_evalDist`.

## Composition

* **`link` congruence in the inner argument**: `link_inner_congr` swaps the
  inner game of a linked composition along a `≡ᵈ`-hop, leveraging
  `Package.run_link_eq_run_shiftLeft`.
* **`par` congruence on both sides**: `par_congr` swaps either factor of
  a `Package.par`-composite along per-handler `evalDist` equalities (one
  per side). The result is a `≡ᵈ`-hop *with the still-open import*
  `I₁ + I₂`, ready to be plugged into a further `link` or `par` step.
-/

universe uᵢ uₘ uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.HeapSSP

namespace Package

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}
  {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, 0} ιᵢ} [I.Fintype] [I.Inhabited]

/-- Two heap-packages sharing an export `E` and an import `I` are
*distributionally equivalent* if they produce the same output distribution
against every client computation, on every output type.

Equivalent characterisations:
* When `I = unifSpec`, the Boolean distinguishing advantage
  `G₀.advantage G₁ A` is zero on every Boolean-valued client `A`
  (`DistEquiv.advantage_zero`).
* For every `α` and every client computation `A : OracleComp E α`,
  `evalDist G₀.run A = evalDist G₁.run A` (the literal definition).

The identifier sets `Ident₀, Ident₁` of the two games are independent: only
the export interface and the resulting output distribution matter from an
client's point of view. -/
def DistEquiv {Ident₀ Ident₁ : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₁]
    (G₀ : Package I E Ident₀) (G₁ : Package I E Ident₁) :
    Prop :=
  ∀ {α : Type} (A : OracleComp E α),
    𝒟[G₀.run A] = 𝒟[G₁.run A]

@[inherit_doc DistEquiv]
scoped infix:50 " ≡ᵈ " => Package.DistEquiv

namespace DistEquiv

variable {Ident Ident₀ Ident₁ Ident₂ : Type}
  [CellSpec.{0, 0} Ident] [CellSpec.{0, 0} Ident₀]
  [CellSpec.{0, 0} Ident₁] [CellSpec.{0, 0} Ident₂]

/-! ### Relation laws -/

@[refl]
protected theorem refl (G : Package I E Ident) : G ≡ᵈ G :=
  fun _ => rfl

@[symm]
protected theorem symm
    {G₀ : Package I E Ident₀} {G₁ : Package I E Ident₁}
    (h : G₀ ≡ᵈ G₁) : G₁ ≡ᵈ G₀ :=
  fun A => (h A).symm

@[trans]
protected theorem trans
    {G₀ : Package I E Ident₀} {G₁ : Package I E Ident₁}
    {G₂ : Package I E Ident₂}
    (h₀₁ : G₀ ≡ᵈ G₁) (h₁₂ : G₁ ≡ᵈ G₂) : G₀ ≡ᵈ G₂ :=
  fun A => (h₀₁ A).trans (h₁₂ A)

instance trans_instance :
    @Trans (Package I E Ident₀) (Package I E Ident₁)
      (Package I E Ident₂) DistEquiv DistEquiv DistEquiv where
  trans := DistEquiv.trans

/-- When the identifier set is fixed, `≡ᵈ` is an `Equivalence`. -/
theorem _root_.VCVio.HeapSSP.Package.equivalence_distEquiv
    (I : OracleSpec.{uᵢ, 0} ιᵢ) [I.Fintype] [I.Inhabited]
    (E : OracleSpec.{uₑ, 0} ιₑ) (Ident : Type) [CellSpec.{0, 0} Ident] :
    Equivalence
      (DistEquiv (I := I) (E := E) (Ident₀ := Ident) (Ident₁ := Ident)) where
  refl := DistEquiv.refl
  symm := DistEquiv.symm
  trans := DistEquiv.trans

/-! ### Constructors -/

/-- Build a `DistEquiv` from the literal per-client `evalDist` equality.
The unfolded definition, exposed for clients that already have the
distribution equality in hand. -/
theorem of_run_evalDist
    {G₀ : Package I E Ident₀} {G₁ : Package I E Ident₁}
    (h : ∀ {α : Type} (A : OracleComp E α),
        𝒟[G₀.run A] = 𝒟[G₁.run A]) :
    G₀ ≡ᵈ G₁ := h

/-- Recover the per-client `evalDist` equality from a `DistEquiv`
witness. The inverse of `of_run_evalDist`. -/
theorem run_evalDist_eq
    {G₀ : Package I E Ident₀} {G₁ : Package I E Ident₁}
    (h : G₀ ≡ᵈ G₁) {α : Type} (A : OracleComp E α) :
    𝒟[G₀.run A] = 𝒟[G₁.run A] := h A

/-- Build a `DistEquiv` from a per-client *propositional* equality at
the `Package.run` level. -/
theorem of_run_eq
    {G₀ : Package I E Ident₀} {G₁ : Package I E Ident₁}
    (h : ∀ {α : Type} (A : OracleComp E α), G₀.run A = G₁.run A) :
    G₀ ≡ᵈ G₁ :=
  fun A => by rw [h A]

/-- **Step constructor (same identifier set).** Two heap-packages with
identical identifier set are distributionally equivalent if their inits
agree under `evalDist` and their per-query handlers agree under `evalDist`
on every heap.

The lemma form of `Package.simulateQ_StateT_evalDist_congr` from
`VCVio.HeapSSP.Advantage`, lifted to the package level: the per-handler
hypothesis discharges the simulation step, and the init hypothesis
discharges the setup step. -/
theorem of_step {G₀ G₁ : Package I E Ident}
    (h_init : 𝒟[G₀.init] = 𝒟[G₁.init])
    (h_impl : ∀ (q : E.Domain) (h : Heap Ident),
        𝒟[(G₀.impl q).run h] = 𝒟[(G₁.impl q).run h]) :
    G₀ ≡ᵈ G₁ := by
  intro α A
  unfold Package.run
  rw [evalDist_bind, evalDist_bind, h_init]
  refine bind_congr fun s₀ => ?_
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  exact simulateQ_StateT_evalDist_congr h_impl A s₀

/-- **Step constructor (under heap bijection).** Two heap-packages with
isomorphic *heap types* `Heap Ident₀ ≃ Heap Ident₁` are distributionally
equivalent if their inits agree under `evalDist` modulo the bijection
(RHS init is mapped through `φ.symm`) and their per-query handlers agree
under `evalDist` modulo the bijection (RHS handler output is mapped
through `Prod.map id φ.symm`).

The lemma form of `Package.simulateQ_StateT_evalDist_congr_of_bij` from
`VCVio.HeapSSP.Advantage`, lifted to the package level. The bijection is
on the *underlying state* (here `Heap Ident`) rather than on identifier
sets directly, so it accommodates the canonical
`Heap.split : Heap (α ⊕ β) ≃ Heap α × Heap β` reshape used by
`par`-composed packages. -/
theorem of_step_bij
    (G₀ : Package I E Ident₀) (G₁ : Package I E Ident₁)
    (φ : Heap Ident₀ ≃ Heap Ident₁)
    (h_init : 𝒟[G₀.init] = 𝒟[φ.symm <$> G₁.init])
    (h_impl : ∀ (q : E.Domain) (h : Heap Ident₀),
        𝒟[(G₀.impl q).run h] =
          𝒟[Prod.map id φ.symm <$> (G₁.impl q).run (φ h)]) :
    G₀ ≡ᵈ G₁ := by
  intro α A
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

/-! ### Bridge to `Package.advantage` (probability-only case)

`Package.advantage` is `unifSpec`-tied (it uses `boolDistAdvantage` on
`ProbComp`), so the bridge lemmas below specialise the import `I` to
`unifSpec`. They are statements about `≡ᵈ`-hops at the `unifSpec`-imports
layer; the *general* import-polymorphic `≡ᵈ` machinery above (especially
`par_congr`) lives one layer below. -/

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
the outer reduction `P` is absorbed into the shifted client
`P.shiftLeft A`, and the equivalence on the inner game closes the proof.

This is the perfect inner-game replacement rule for linked packages. -/
theorem link_inner_congr (P : Package M E Ident_P)
    {Q₀ : Package I M Ident₀} {Q₁ : Package I M Ident₁}
    (h : Q₀ ≡ᵈ Q₁) :
    P.link Q₀ ≡ᵈ P.link Q₁ := by
  intro α A
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]
  exact h (P.shiftLeft A)

end LinkCongr

end DistEquiv

end Package

/-! ### Compositional congruences (`par`)

Stated outside `namespace Package` because we need fresh import / export
variables `I₁, I₂, E₁, E₂` for the two factors that are independent of
the ambient `I, E`. -/

namespace Package

namespace DistEquiv

section ParCongr

variable {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ}
  {I₁ : OracleSpec.{uᵢ, 0} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, 0} ιᵢ₂}
  [I₁.Fintype] [I₁.Inhabited] [I₂.Fintype] [I₂.Inhabited]
  {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {E₁ : OracleSpec.{uₑ, 0} ιₑ₁} {E₂ : OracleSpec.{uₑ, 0} ιₑ₂}
  {α β : Type} [CellSpec.{0, 0} α] [CellSpec.{0, 0} β]

/-- **`par` congruence on both sides.** Two `par`-composites are
distributionally equivalent (over the *open* import `I₁ + I₂`) if their
factor inits and per-handler outputs agree under `evalDist` componentwise.

The proof reduces to `of_step` on the parallel package: the init step
collapses through `evalDist_bind`/`evalDist_liftComp` to the per-factor
init equalities; each query case (left or right) collapses through the
parametric `par_impl_*_apply_run` lemmas to the corresponding per-factor
handler equality, with the *other* factor's heap component threaded
through unchanged. The hypotheses are stated factorwise — one
`(init, impl)` pair per side — to exactly match the shape of typical
`Package.par`-cutover proofs (e.g. parallel OTP channels). -/
theorem par_congr
    {p₁ p₁' : Package I₁ E₁ α} {p₂ p₂' : Package I₂ E₂ β}
    (h₁_init : 𝒟[p₁.init] = 𝒟[p₁'.init])
    (h₁_impl : ∀ (q : E₁.Domain) (h : Heap α),
        𝒟[(p₁.impl q).run h] = 𝒟[(p₁'.impl q).run h])
    (h₂_init : 𝒟[p₂.init] = 𝒟[p₂'.init])
    (h₂_impl : ∀ (q : E₂.Domain) (h : Heap β),
        𝒟[(p₂.impl q).run h] = 𝒟[(p₂'.impl q).run h]) :
    p₁.par p₂ ≡ᵈ p₁'.par p₂' := by
  refine of_step ?_ ?_
  · -- Init equivalence: rewrite `par`'s init into nested binds and apply
    -- the per-factor init equalities pointwise under `evalDist_bind`.
    rw [par_init, par_init]
    rw [evalDist_bind, evalDist_bind, evalDist_liftComp, evalDist_liftComp,
      h₁_init]
    refine bind_congr fun h_α => ?_
    rw [evalDist_bind, evalDist_bind, evalDist_liftComp, evalDist_liftComp,
      h₂_init]
  · -- Per-query handler equivalence: split on the sum index. Both sides of
    -- `par.impl` reduce *definitionally* (after `let`-substitution of the
    -- `Heap.split` projections of `h`) to the same `Prod.map`-shaped lift
    -- of the corresponding factor's handler. We expose that shared shape
    -- with `change`, then close with `evalDist_map_eq_of_evalDist_eq` on
    -- the `liftComp`-of-handler equality, which itself follows from the
    -- factor's `h_impl` hypothesis under `evalDist_liftComp`.
    intro q h
    rcases q with t | t
    · -- Left channel.
      change 𝒟[
          (Prod.map id (fun h_α' =>
              (Heap.split α β).symm (h_α', (Heap.split α β h).2))) <$>
            liftComp ((p₁.impl t).run (Heap.split α β h).1) (I₁ + I₂)] =
        𝒟[
          (Prod.map id (fun h_α' =>
              (Heap.split α β).symm (h_α', (Heap.split α β h).2))) <$>
            liftComp ((p₁'.impl t).run (Heap.split α β h).1) (I₁ + I₂)]
      refine evalDist_map_eq_of_evalDist_eq ?_ _
      rw [evalDist_liftComp, evalDist_liftComp]
      exact h₁_impl t _
    · -- Right channel: dual to the left case.
      change 𝒟[
          (Prod.map id (fun h_β' =>
              (Heap.split α β).symm ((Heap.split α β h).1, h_β'))) <$>
            liftComp ((p₂.impl t).run (Heap.split α β h).2) (I₁ + I₂)] =
        𝒟[
          (Prod.map id (fun h_β' =>
              (Heap.split α β).symm ((Heap.split α β h).1, h_β'))) <$>
            liftComp ((p₂'.impl t).run (Heap.split α β h).2) (I₁ + I₂)]
      refine evalDist_map_eq_of_evalDist_eq ?_ _
      rw [evalDist_liftComp, evalDist_liftComp]
      exact h₂_impl t _

end ParCongr

end DistEquiv

end Package

end VCVio.HeapSSP
