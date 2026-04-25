/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Package
import VCVio.OracleComp.Coercions.Add

/-!
# HeapSSP: Composition of heap-packages

Sequential `link` and parallel `par` for `HeapSSP.Package`.

Composed packages use the disjoint sum of their identifier sets. The
canonical state form is `Heap (α ⊕ β)`, while `Heap.split α β` exposes the
two component heaps when running one side of the composition. The main
reduction lemma, `run_link_eq_run_shiftLeft`, states that running a linked
package is the same as running the inner package against the outer package
absorbed into the client computation. -/

universe uᵢ uₘ uₑ uₛ vᵢ v

open OracleSpec OracleComp

namespace VCVio.HeapSSP

namespace Package

variable {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
  {I : OracleSpec.{uᵢ, vᵢ} ιᵢ}
  {M : OracleSpec.{uₘ, max uₛ v} ιₘ}
  {E : OracleSpec.{uₑ, max uₛ v} ιₑ}
  {α β : Type uₛ} [CellSpec.{uₛ, v} α] [CellSpec.{uₛ, v} β]

/-! ### Sequential composition (`link`) -/

/-- The reshape `(γ × Heap α) × Heap β → γ × Heap (α ⊕ β)` used by the linked
package's handler to splice the outer and inner heap factors into the
composite heap on the disjoint sum of identifier sets.

`@[reducible]` so downstream proofs can unfold it into the concrete lambda
without additional rewriting. -/
@[reducible]
def linkReshape {γ : Type (max uₛ v)} :
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

/-! ### Forwarding reduction for `link`

If the outer handler on query `t` is a pure *forwarder* over some
oracle computation `q : OracleComp M (E.Range t)` (i.e. it is
`fun h_α => (fun a => (a, h_α)) <$> q`, threading `h_α` through
unchanged), the linked handler reduces to one `<$>` over
`simulateQ inner.impl q` with the outer heap `h_α` re-inserted via
`(Heap.split α β).symm`. This captures the common "outer just delegates"
pattern that shows up whenever a reduction package only touches a
single inner channel on a given query. -/

/-- Closed form for the linked handler on a query whose outer handler is a
pure forwarder through `q : OracleComp M (E.Range t)`. The linked result on
heap `(Heap.split α β).symm (h_α, h_β)` is one reshape over the inner
simulation of `q`, with `h_α` threaded back via `(Heap.split α β).symm`. -/
lemma link_impl_apply_run_of_outer_forward
    (outer : Package M E α) (inner : Package I M β)
    (t : E.Domain) (q : OracleComp M (E.Range t))
    (houter : outer.impl t =
      StateT.mk fun h_α => (fun a => (a, h_α)) <$> q)
    (h_α : Heap α) (h_β : Heap β) :
    ((outer.link inner).impl t).run ((Heap.split α β).symm (h_α, h_β)) =
      (fun (p : E.Range t × Heap β) =>
        (p.1, (Heap.split α β).symm (h_α, p.2))) <$>
          (simulateQ inner.impl q).run h_β := by
  rw [link_impl_apply_run, houter]
  simp only [StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map,
    linkReshape]

/-! ### `link` reduction lemma (parametric in the heap factors) -/

/-- Structural fact: running `(P.link Q).impl` against a client computation `A`,
starting from a composite heap `(Heap.split α β).symm (h_α, h_β)`, is the
same as nesting the simulations and reshaping via `linkReshape`.

The parametric starting heap exposes the two component heaps explicitly, so
the `Heap.split` projections collapse definitionally during the proof. -/
theorem simulateQ_link_run {γ : Type (max uₛ v)}
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

/-! ### Shifted clients and the link reduction -/

/-- The shifted client obtained by absorbing the outer package `P` into the
client computation. -/
def shiftLeft (P : Package M E α) {γ : Type (max uₛ v)} (A : OracleComp E γ) :
    OracleComp M γ :=
  P.init >>= fun h_α => Prod.fst <$> (simulateQ P.impl A).run h_α

@[simp]
lemma shiftLeft_pure (P : Package M E α) {γ : Type (max uₛ v)} (x : γ) :
    P.shiftLeft (pure x) = P.init >>= fun _ => pure x := by
  simp [shiftLeft, simulateQ_pure, StateT.run_pure, bind_pure_comp]

lemma shiftLeft_map (P : Package M E α) {γ δ : Type (max uₛ v)} (f : γ → δ)
    (A : OracleComp E γ) :
    P.shiftLeft (f <$> A) = f <$> P.shiftLeft A := by
  unfold Package.shiftLeft
  rw [map_bind, simulateQ_map]
  refine bind_congr fun h_α => ?_
  rw [StateT.run_map, Functor.map_map, Functor.map_map]

lemma shiftLeft_bind (P : Package M E α) {γ δ : Type (max uₛ v)}
    (A : OracleComp E γ) (f : γ → OracleComp E δ) :
    P.shiftLeft (A >>= f) =
      P.init >>= fun h_α =>
        (simulateQ P.impl A).run h_α >>= fun (a, h_α') =>
          Prod.fst <$> (simulateQ P.impl (f a)).run h_α' := by
  unfold Package.shiftLeft
  simp [simulateQ_bind, StateT.run_bind, map_bind]

/-- **Link reduction, program form.** Running the linked game `P.link Q`
against client computation `A` produces the same `OracleComp` distribution as
running the inner game `Q` against the shifted client `P.shiftLeft A`.
The outer package is absorbed into the client, leaving the inner package as the
only game being run. -/
theorem run_link_eq_run_shiftLeft {γ : Type (max uₛ v)}
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

/-! ### Parallel composition (`par`) -/

variable {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {I₁ : OracleSpec.{uᵢ, max uₛ v} ιᵢ₁} {I₂ : OracleSpec.{uᵢ, max uₛ v} ιᵢ₂}
  {E₁ : OracleSpec.{uₑ, max uₛ v} ιₑ₁} {E₂ : OracleSpec.{uₑ, max uₛ v} ιₑ₂}

/-- Parallel composition of two heap-packages.

Given `p₁` exporting `E₁`, importing `I₁`, with identifier set `α`; and
`p₂` exporting `E₂`, importing `I₂`, with identifier set `β`; the parallel
composite exports `E₁ + E₂`, imports `I₁ + I₂`, and has identifier set
`α ⊕ β` with composite state `Heap (α ⊕ β)`.

State separation is automatic: each side's handler runs on its component heap,
and the result is rebuilt into the composite heap. -/
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

/-- Parametric form of `(par p₁ p₂).impl (Sum.inl t)` applied to a heap built
from `(Heap.split α β).symm (h_α, h_β)`. The `Heap.split` projections inside
the parallel handler collapse via the right-inverse of `Heap.split`, leaving
a clean expression in `h_α` and `h_β`. -/
lemma par_impl_inl_apply_run
    (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β)
    (t : E₁.Domain) (h_α : Heap α) (h_β : Heap β) :
    ((p₁.par p₂).impl (Sum.inl t)).run ((Heap.split α β).symm (h_α, h_β)) =
      (Prod.map id (fun h_α' => (Heap.split α β).symm (h_α', h_β))) <$>
        liftComp ((p₁.impl t).run h_α) (I₁ + I₂) := rfl

/-- Parametric form of `(par p₁ p₂).impl (Sum.inr t)` applied to a heap built
from `(Heap.split α β).symm (h_α, h_β)`. -/
lemma par_impl_inr_apply_run
    (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β)
    (t : E₂.Domain) (h_α : Heap α) (h_β : Heap β) :
    ((p₁.par p₂).impl (Sum.inr t)).run ((Heap.split α β).symm (h_α, h_β)) =
      (Prod.map id (fun h_β' => (Heap.split α β).symm (h_α, h_β'))) <$>
        liftComp ((p₂.impl t).run h_β) (I₁ + I₂) := rfl

/-- Closed form for simulating a single left-channel query against the parallel
handler, on a heap of the split-canonical shape.

The composite `simulateQ` of the lifted query reduces to `liftComp` of the
corresponding single-channel `(p₁.impl t).run h_α`, with the right-half heap
`h_β` threaded through unchanged via `(Heap.split α β).symm`. This bundles
`simulateQ_spec_query` (which removes the `id <$>` artifact in parametric
sum-spec contexts) with `par_impl_inl_apply_run` (which collapses the
`Heap.split` projections inside the parallel handler).

Stated in `.run` form to match the shape produced by `StateT.run_bind`, which
leaves `(simulateQ ... (liftM ...)).run state_arg` on the proof state.

Using this lemma directly is the canonical way to step a left-channel client
query through `Package.par.run`; without it, one has to manage the
`simulateQ`/`<$>`/`StateT.run` interleaving by hand. -/
@[simp]
lemma simulateQ_par_query_inl_run
    (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β)
    (t : E₁.Domain) (h_α : Heap α) (h_β : Heap β) :
    (simulateQ (p₁.par p₂).impl
        (liftM ((E₁ + E₂).query (Sum.inl t)))).run
      ((Heap.split α β).symm (h_α, h_β)) =
        (Prod.map id (fun h_α' => (Heap.split α β).symm (h_α', h_β))) <$>
          liftComp ((p₁.impl t).run h_α) (I₁ + I₂) := by
  rw [simulateQ_spec_query]
  exact par_impl_inl_apply_run p₁ p₂ t h_α h_β

/-- Closed form for simulating a single right-channel query against the
parallel handler, dual to `simulateQ_par_query_inl_run`. -/
@[simp]
lemma simulateQ_par_query_inr_run
    (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β)
    (t : E₂.Domain) (h_α : Heap α) (h_β : Heap β) :
    (simulateQ (p₁.par p₂).impl
        (liftM ((E₁ + E₂).query (Sum.inr t)))).run
      ((Heap.split α β).symm (h_α, h_β)) =
        (Prod.map id (fun h_β' => (Heap.split α β).symm (h_α, h_β'))) <$>
          liftComp ((p₂.impl t).run h_β) (I₁ + I₂) := by
  rw [simulateQ_spec_query]
  exact par_impl_inr_apply_run p₁ p₂ t h_α h_β

end Package

/-! ### Universe-polymorphism sanity checks for `link` and `par` -/

section UniverseTests

example {ιᵢ : Type uᵢ} {ιₘ : Type uₘ} {ιₑ : Type uₑ}
    {I : OracleSpec.{uᵢ, vᵢ} ιᵢ}
    {M : OracleSpec.{uₘ, max uₛ v} ιₘ}
    {E : OracleSpec.{uₑ, max uₛ v} ιₑ}
    {α β : Type uₛ} [CellSpec.{uₛ, v} α] [CellSpec.{uₛ, v} β]
    (P : Package M E α) (Q : Package I M β) :
    Package I E (α ⊕ β) := P.link Q

example {ιᵢ₁ : Type uᵢ} {ιᵢ₂ : Type uᵢ} {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
    {I₁ : OracleSpec.{uᵢ, max uₛ v} ιᵢ₁}
    {I₂ : OracleSpec.{uᵢ, max uₛ v} ιᵢ₂}
    {E₁ : OracleSpec.{uₑ, max uₛ v} ιₑ₁}
    {E₂ : OracleSpec.{uₑ, max uₛ v} ιₑ₂}
    {α β : Type uₛ} [CellSpec.{uₛ, v} α] [CellSpec.{uₛ, v} β]
    (p₁ : Package I₁ E₁ α) (p₂ : Package I₂ E₂ β) :
    Package (I₁ + I₂) (E₁ + E₂) (α ⊕ β) := p₁.par p₂

end UniverseTests

end VCVio.HeapSSP
