/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Package
import VCVio.OracleComp.Coercions.Add

/-!
# HeapSSP: Composition of heap-packages

Sequential `link` and parallel `par` for `HeapSSP.Package`, and the
program-level reduction lemma `run_link_eq_run_shiftLeft` analogous to its
counterpart in `VCVio.SSP.Composition`.

Key differences from `VCVio.SSP.Composition`:

* The state of a composed package is `Heap (α ⊕ β)`, *not* `Heap α × Heap β`.
  The two are isomorphic via `Heap.split α β` (an `Equiv`), but the canonical
  form is the heap on the disjoint sum of identifier sets.
* `linkReshape : (γ × Heap α) × Heap β → γ × Heap (α ⊕ β)` plays the role of
  the SSP version's `(γ × σ₁) × σ₂ → γ × (σ₁ × σ₂)`. It uses
  `(Heap.split α β).symm` to rebuild the composite heap.
* The reduction lemma `simulateQ_link_run` is stated in *parametric* form,
  i.e. with the heap given as `(Heap.split α β).symm (h_α, h_β)`. This makes
  the LHS and RHS match shape-for-shape with the SSP version and lets the
  proof carry over unchanged. The "raw" form
  `(simulateQ (P.link Q).impl A).run h` is recovered by setting
  `(h_α, h_β) := Heap.split α β h`.

Per-cell frame reasoning for the composed package follows directly from
`Heap.split_apply_inl/inr` together with the `get_update_of_ne` lemmas in
`VCVio/HeapSSP/Heap.lean`. -/

universe uᵢ uₘ uₑ vᵢ v

open OracleSpec OracleComp

namespace VCVio.HeapSSP

namespace Package

variable {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
  {α β : Type} [CellSpec.{0, v} α] [CellSpec.{0, v} β]

/-! ### Sequential composition (`link`) -/

/-- The reshape `(γ × Heap α) × Heap β → γ × Heap (α ⊕ β)` used by the linked
package's handler to splice the outer and inner heap factors into the
composite heap on the disjoint sum of identifier sets.

`@[reducible]` so downstream proofs can unfold it into the concrete lambda
without additional rewriting. -/
@[reducible]
def linkReshape {γ : Type v} :
    (γ × Heap α) × Heap β → γ × Heap (α ⊕ β) :=
  fun p => (p.1.1, (Heap.split α β).symm (p.1.2, p.2))

/-- Sequential composition of two heap-packages: `outer ∘ inner`.

The outer package exports `E` and imports `M` over identifier set `α`. The
inner package exports `M` and imports `I` over identifier set `β`. The
composite exports `E` and imports `I`, with identifier set `α ⊕ β` and state
`Heap (α ⊕ β)` (outer heap on the `inl` side, inner heap on the `inr`
side).

* **Init.** The composite init lives in `OracleComp I (Heap (α ⊕ β))`. The
  outer init `outer.init : OracleComp M (Heap α)` may query `M`, so we
  simulate it against `inner.impl` starting from `inner.init`'s initial
  inner heap, then rebuild the composite heap via `(Heap.split α β).symm`.
* **Handler.** Each export query of the composite splits the heap into
  `(h_α, h_β)`, runs the outer handler in `h_α`, re-interprets every
  import-query in `M` it issues by running the inner handler in `h_β`,
  and rebuilds the composite heap. -/
def link (outer : Package M E α) (inner : Package I M β) : Package I E (α ⊕ β) where
  init := do
    let h_β₀ ← inner.init
    let (h_α₀, h_β₀') ← (simulateQ inner.impl outer.init).run h_β₀
    pure ((Heap.split α β).symm (h_α₀, h_β₀'))
  impl t := StateT.mk fun h =>
    let h_α := (Heap.split α β h).1
    let h_β := (Heap.split α β h).2
    let outerStep : OracleComp M (E.Range t × Heap α) := (outer.impl t).run h_α
    let innerStep : OracleComp I ((E.Range t × Heap α) × Heap β) :=
      (simulateQ inner.impl outerStep).run h_β
    linkReshape <$> innerStep

@[simp]
lemma link_init (outer : Package M E α) (inner : Package I M β) :
    (outer.link inner).init =
      inner.init >>= fun h_β₀ =>
        (simulateQ inner.impl outer.init).run h_β₀ >>= fun (h_α₀, h_β₀') =>
          pure ((Heap.split α β).symm (h_α₀, h_β₀')) := rfl

/-- Parametric form of `(link outer inner).impl t` applied to a heap of the
form `(Heap.split α β).symm (h_α, h_β)`. The `Heap.split` projections inside
`link.impl` collapse via the right-inverse of `Heap.split`, leaving a clean
expression in terms of `h_α` and `h_β`. -/
lemma link_impl_apply_run (outer : Package M E α) (inner : Package I M β)
    (t : E.Domain) (h_α : Heap α) (h_β : Heap β) :
    ((outer.link inner).impl t).run ((Heap.split α β).symm (h_α, h_β)) =
      linkReshape <$> (simulateQ inner.impl ((outer.impl t).run h_α)).run h_β := rfl

/-! ### `link` reduction lemma (parametric in the heap factors) -/

/-- Structural fact: running `(P.link Q).impl` against an adversary `A`,
starting from a composite heap `(Heap.split α β).symm (h_α, h_β)`, is the
same as nesting the simulations and reshaping via `linkReshape`.

This is the parametric form of the SSP `simulateQ_link_run`; the difference
is that the composite state is built from `(h_α, h_β)` via `Heap.split.symm`
rather than being literally a pair `(s₁, s₂)`. The proof follows the same
structure as the SSP version, with the `Heap.split` projections collapsing
definitionally on `(Heap.split α β).symm (h_α, h_β)`. -/
theorem simulateQ_link_run {γ : Type v}
    (P : Package M E α) (Q : Package I M β)
    (A : OracleComp E γ) (h_α : Heap α) (h_β : Heap β) :
    (simulateQ (P.link Q).impl A).run ((Heap.split α β).symm (h_α, h_β)) =
      linkReshape <$>
        (simulateQ Q.impl ((simulateQ P.impl A).run h_α)).run h_β := by
  induction A using OracleComp.inductionOn generalizing h_α h_β with
  | pure x =>
    change (pure (x, (Heap.split α β).symm (h_α, h_β))
        : OracleComp I (γ × Heap (α ⊕ β))) =
      linkReshape <$> (simulateQ Q.impl (pure (x, h_α))).run h_β
    rw [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    have hLHS :
        (simulateQ (P.link Q).impl (liftM (query t) >>= k)).run
            ((Heap.split α β).symm (h_α, h_β)) =
          (simulateQ Q.impl ((P.impl t).run h_α)).run h_β >>=
            fun (p : (E.Range t × Heap α) × Heap β) =>
              (simulateQ (P.link Q).impl (k p.1.1)).run
                ((Heap.split α β).symm (p.1.2, p.2)) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change ((P.link Q).impl t >>= fun a =>
          simulateQ (P.link Q).impl (k a)).run
            ((Heap.split α β).symm (h_α, h_β)) = _
      rw [StateT.run_bind]
      change (linkReshape <$>
          (simulateQ Q.impl ((P.impl t).run h_α)).run h_β) >>= _ = _
      rw [bind_map_left]
    have hRHS :
        (simulateQ Q.impl ((simulateQ P.impl (liftM (query t) >>= k)).run h_α)).run h_β =
          (simulateQ Q.impl ((P.impl t).run h_α)).run h_β >>=
            fun (p : (E.Range t × Heap α) × Heap β) =>
              (simulateQ Q.impl ((simulateQ P.impl (k p.1.1)).run p.1.2)).run p.2 := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change (simulateQ Q.impl ((P.impl t >>=
          fun a => simulateQ P.impl (k a)).run h_α)).run h_β = _
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
    rw [hLHS, hRHS, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1.1 p.1.2 p.2

/-! ### Shifted adversary and the program-level SSP reduction -/

/-- The **shifted adversary** obtained by absorbing the outer reduction
package `P` into the adversary. Identical in shape to its `VCVio.SSP`
counterpart; only the state type changes (`Heap α` instead of `σ₁`). -/
def shiftLeft (P : Package M E α) {γ : Type v} (A : OracleComp E γ) :
    OracleComp M γ :=
  P.init >>= fun h_α => Prod.fst <$> (simulateQ P.impl A).run h_α

@[simp]
lemma shiftLeft_pure (P : Package M E α) {γ : Type v} (x : γ) :
    P.shiftLeft (pure x) = P.init >>= fun _ => pure x := by
  simp [shiftLeft, simulateQ_pure, StateT.run_pure, bind_pure_comp]

lemma shiftLeft_map (P : Package M E α) {γ δ : Type v} (f : γ → δ)
    (A : OracleComp E γ) :
    P.shiftLeft (f <$> A) = f <$> P.shiftLeft A := by
  unfold Package.shiftLeft
  rw [map_bind, simulateQ_map]
  refine bind_congr fun h_α => ?_
  rw [StateT.run_map, Functor.map_map, Functor.map_map]

/-- **SSP reduction (program form).** Running the linked game `P.link Q`
against adversary `A` produces the same `OracleComp` distribution as
running the inner game `Q` against the shifted adversary `P.shiftLeft A`.

Structurally identical to `VCVio.SSP.Package.run_link_eq_run_shiftLeft`;
the only differences are the state type (`Heap (α ⊕ β)` instead of
`σ₁ × σ₂`) and the reshape (`(Heap.split α β).symm` instead of pairing). -/
theorem run_link_eq_run_shiftLeft {γ : Type v}
    (P : Package M E α) (Q : Package I M β) (A : OracleComp E γ) :
    (P.link Q).run A = Q.run (P.shiftLeft A) := by
  -- Both sides reduce to `Q.runState P.init >>= F` for the same `F`.
  set F : Heap α × Heap β → OracleComp I γ := fun phs =>
    (fun x : (γ × Heap α) × Heap β => x.1.1) <$>
      (simulateQ Q.impl ((simulateQ P.impl A).run phs.1)).run phs.2 with hF
  have hLHS : (P.link Q).run A = Q.runState P.init >>= F := by
    unfold Package.run Package.runState
    rw [link_init]
    simp only [bind_assoc]
    refine bind_congr fun h_β₀ => ?_
    refine bind_congr fun phs => ?_
    obtain ⟨h_α, h_β⟩ := phs
    rw [pure_bind, StateT.run'_eq, simulateQ_link_run]
    simp [hF, Functor.map_map]
  have hRHS : Q.run (P.shiftLeft A) = Q.runState P.init >>= F := by
    change Q.init >>= (fun h_β₀ => (simulateQ Q.impl (P.shiftLeft A)).run' h_β₀) = _
    unfold Package.shiftLeft
    simp only [StateT.run'_eq, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      map_bind, Package.runState, bind_assoc]
    refine bind_congr fun h_β => ?_
    refine bind_congr fun phs => ?_
    simp [hF, Functor.map_map]
  rw [hLHS, hRHS]

/-! ### Parallel composition (`par`)

Same shape as `VCVio.SSP.Package.par`, with composite identifier set
`α ⊕ β` and composite state `Heap (α ⊕ β)`. -/

variable {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
  {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}

/-- Parallel composition of two heap-packages.

Given `p₁` exporting `E₁`, importing `I₁`, with identifier set `α`; and
`p₂` exporting `E₂`, importing `I₂`, with identifier set `β`; the parallel
composite exports `E₁ + E₂`, imports `I₁ + I₂`, and has identifier set
`α ⊕ β` with composite state `Heap (α ⊕ β)`.

State separation is automatic: each side's handler reads/writes only its
own component (`Heap.split α β _`'s `.1` for `p₁`, `.2` for `p₂`). This is
the structural-typing counterpart of SSProve's `fseparate` side-condition,
specialized to the heap framework. -/
def par (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β) :
    Package (I₁ + I₂) (E₁ + E₂) (α ⊕ β) where
  init := do
    let h_α ← liftComp p₁.init (I₁ + I₂)
    let h_β ← liftComp p₂.init (I₁ + I₂)
    pure ((Heap.split α β).symm (h_α, h_β))
  impl
    | .inl t => StateT.mk fun h =>
        let h_α := (Heap.split α β h).1
        let h_β := (Heap.split α β h).2
        (Prod.map id (fun h_α' => (Heap.split α β).symm (h_α', h_β))) <$>
          liftComp ((p₁.impl t).run h_α) (I₁ + I₂)
    | .inr t => StateT.mk fun h =>
        let h_α := (Heap.split α β h).1
        let h_β := (Heap.split α β h).2
        (Prod.map id (fun h_β' => (Heap.split α β).symm (h_α, h_β'))) <$>
          liftComp ((p₂.impl t).run h_β) (I₁ + I₂)

@[simp]
lemma par_init (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β) :
    (p₁.par p₂).init =
      liftComp p₁.init (I₁ + I₂) >>= fun h_α =>
      liftComp p₂.init (I₁ + I₂) >>= fun h_β =>
      pure ((Heap.split α β).symm (h_α, h_β)) := rfl

end Package

/-! ### Universe-polymorphism sanity checks for `link` and `par` -/

section UniverseTests

example {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ} {M : OracleSpec.{uₘ, v} ιₘ} {E : OracleSpec.{uₑ, v} ιₑ}
    {α β : Type} [CellSpec.{0, v} α] [CellSpec.{0, v} β]
    (P : Package M E α) (Q : Package I M β) :
    Package I E (α ⊕ β) := P.link Q

example {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
    {I₁ : OracleSpec.{uᵢ, v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, v} ιᵢ₂}
    {E₁ : OracleSpec.{uₑ, v} ιₑ₁} {E₂ : OracleSpec.{uₑ, v} ιₑ₂}
    {α β : Type} [CellSpec.{0, v} α] [CellSpec.{0, v} β]
    (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β) :
    Package (I₁ + I₂) (E₁ + E₂) (α ⊕ β) := p₁.par p₂

end UniverseTests

end VCVio.HeapSSP
