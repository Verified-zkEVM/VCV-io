/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Sim.Defs
public import ToMathlib.ITree.Bisim.Bind

/-! # Naturality lemmas for `ITree.simulate` and `ITree.mapSpec`

The standard equational theory for the simulation operators:

* `simulate_pure`, `simulate_step`, `simulate_query` — one-step unfoldings
  recording the action of `simulate` on each `Shape` constructor.
* `simulate_bind` — `simulate` distributes over `bind`.
* `simulate_id` — interpreting via the trivial handler is (weakly) the
  identity.
* `mapSpec_pure`, `mapSpec_step`, `mapSpec_query` — one-step unfoldings of
  `mapSpec`.
* `mapSpec_id`, `mapSpec_comp` — functoriality of `mapSpec` over the lens
  category on `PFunctor`.
* `simulate_ofLens` — relating `simulate` and `mapSpec` on a renaming.

The proofs are scaffolded with `sorry`; they reduce to one-step `M.corec`
unfoldings combined with the (sorry-blocked) bisimulation laws of
`ToMathlib.ITree.Bisim.Bind`.
-/

@[expose] public section

universe u

namespace ITree

variable {E F G : PFunctor.{u, u}} {α β : Type u}

/-! ### One-step unfoldings of `simulate` -/

/-- Step transformer used internally by `simulate`. -/
private def simulateStep (h : Handler E F) :
    ITree E α → ITree F (ITree E α ⊕ α) := fun t =>
  match shape' t with
  | ⟨.pure r, _⟩ => pure (.inr r)
  | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
  | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))

private theorem simulate_eq_iter (h : Handler E F) (t : ITree E α) :
    simulate h t = iter (simulateStep h) t := rfl

private theorem simulateStep_pure (h : Handler E F) (r : α) :
    simulateStep h (pure (F := E) r) = (pure (.inr r) : ITree F (ITree E α ⊕ α)) := by
  change (match shape' (pure (F := E) r) with
      | ⟨.pure r, _⟩ => (pure (.inr r) : ITree F (ITree E α ⊕ α))
      | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
      | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))) = pure (.inr r)
  rw [shape'_pure]

theorem simulate_pure (h : Handler E F) (r : α) :
    simulate h (pure (F := E) r) = pure r := by
  apply PFunctor.M.eq_of_dest_eq
  rw [simulate_eq_iter, iter, PFunctor.M.dest_corec_eq _ _
      (show iterStep (simulateStep h) (simulateStep h (pure r)) =
            ⟨.pure r, PEmpty.elim⟩ by
        rw [simulateStep_pure]
        change (match PFunctor.M.dest (pure (.inr r) : ITree F (ITree E α ⊕ α)) with
          | ⟨.pure (.inl j), _⟩ => (⟨.step, fun _ => simulateStep h j⟩ :
              (Poly F α).Obj (ITree F (ITree E α ⊕ α)))
          | ⟨.pure (.inr r), _⟩ => ⟨.pure r, PEmpty.elim⟩
          | ⟨.step, c⟩ => ⟨.step, fun u => c u⟩
          | ⟨.query a, c⟩ => ⟨.query a, fun b => c b⟩) = ⟨.pure r, PEmpty.elim⟩
        rw [show PFunctor.M.dest (pure (.inr r) : ITree F (ITree E α ⊕ α)) =
          ⟨.pure (.inr r), PEmpty.elim⟩ from shape'_pure _]),
      show PFunctor.M.dest (pure (F := F) r) = ⟨.pure r, PEmpty.elim⟩
        from shape'_pure r]
  congr 1
  funext b
  exact b.elim

private theorem simulateStep_step (h : Handler E F) (t : ITree E α) :
    simulateStep h (step t) = (pure (.inl t) : ITree F (ITree E α ⊕ α)) := by
  change (match shape' (step t) with
      | ⟨.pure r, _⟩ => (pure (.inr r) : ITree F (ITree E α ⊕ α))
      | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
      | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b)))) = pure (.inl t)
  rw [shape'_step]

/-- One-step strong unfolding: `simulate` distributes over a leading silent
step. -/
theorem simulate_step_eq (h : Handler E F) (t : ITree E α) :
    simulate h (step t) = step (simulate h t) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [simulate_eq_iter, iter, PFunctor.M.dest_corec_eq _ _
      (show iterStep (simulateStep h) (simulateStep h (step t)) =
            ⟨.step, fun _ => simulateStep h t⟩ by
        rw [simulateStep_step]
        change (match PFunctor.M.dest (pure (.inl t) : ITree F (ITree E α ⊕ α)) with
          | ⟨.pure (.inl j), _⟩ => (⟨.step, fun _ => simulateStep h j⟩ :
              (Poly F α).Obj (ITree F (ITree E α ⊕ α)))
          | ⟨.pure (.inr r), _⟩ => ⟨.pure r, PEmpty.elim⟩
          | ⟨.step, c⟩ => ⟨.step, fun u => c u⟩
          | ⟨.query a, c⟩ => ⟨.query a, fun b => c b⟩) =
            ⟨.step, fun _ => simulateStep h t⟩
        rw [show PFunctor.M.dest (pure (.inl t) : ITree F (ITree E α ⊕ α)) =
          ⟨.pure (.inl t), PEmpty.elim⟩ from shape'_pure _])]
  show ⟨.step, fun _ => PFunctor.M.corec _ (simulateStep h t)⟩ =
    PFunctor.M.dest (step (simulate h t))
  rw [show PFunctor.M.dest (step (simulate h t)) = ⟨.step, fun _ => simulate h t⟩
      from shape'_step _]
  rfl

theorem simulate_step (h : Handler E F) (t : ITree E α) :
    WeakBisim (simulate h (step t)) (simulate h t) := by
  rw [simulate_step_eq]
  exact step_weakBisim _

theorem simulate_query (h : Handler E F) (a : E.A) (k : E.B a → ITree E α) :
    WeakBisim (simulate h (query a k))
      (bind (h a) (fun b => simulate h (k b))) := by
  sorry

/-! ### `simulate` is monadic and identity-preserving -/

theorem simulate_bind (h : Handler E F) (t : ITree E α) (k : α → ITree E β) :
    WeakBisim (simulate h (bind t k)) (bind (simulate h t) (fun a => simulate h (k a))) := by
  sorry

theorem simulate_id (t : ITree E α) :
    WeakBisim (simulate (Handler.id E) t) t := by
  sorry

/-! ### One-step unfoldings of `mapSpec`

These are direct `M.corec` unfoldings using `dest_corec_eq` and the fact
that `M.dest` is injective (`PFunctor.M.eq_of_dest_eq`). They do **not**
need any bisimulation tooling. -/

@[simp] theorem mapSpec_pure (φ : PFunctor.Lens E F) (r : α) :
    mapSpec φ (pure (F := E) r) = pure r := by
  apply PFunctor.M.eq_of_dest_eq
  rw [mapSpec, PFunctor.M.dest_corec_eq _ _ (mapSpecStep_pure φ r)]
  unfold ITree.pure
  rw [PFunctor.M.dest_mk]
  congr 1
  funext b
  exact b.elim

@[simp] theorem mapSpec_step (φ : PFunctor.Lens E F) (t : ITree E α) :
    mapSpec φ (step t) = step (mapSpec φ t) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [mapSpec, PFunctor.M.dest_corec_eq _ _ (mapSpecStep_step φ t)]
  unfold ITree.step
  rw [PFunctor.M.dest_mk]

@[simp] theorem mapSpec_query (φ : PFunctor.Lens E F) (a : E.A) (k : E.B a → ITree E α) :
    mapSpec φ (query a k) =
      query (φ.toFunA a) (fun b => mapSpec φ (k (φ.toFunB a b))) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [mapSpec, PFunctor.M.dest_corec_eq _ _ (mapSpecStep_query φ a k)]
  unfold ITree.query
  rw [PFunctor.M.dest_mk]

/-! ### Functoriality of `mapSpec` -/

theorem mapSpec_id (t : ITree E α) :
    mapSpec (PFunctor.Lens.id E) t = t := by
  conv_rhs => rw [← PFunctor.M.corec_dest t]
  refine PFunctor.M.corec_eq_corec
    (mapSpecStep (PFunctor.Lens.id E)) PFunctor.M.dest Eq t t rfl ?_
  rintro u v rfl
  rcases h : PFunctor.M.dest u with ⟨sh, c⟩
  cases sh with
  | pure r =>
      refine ⟨.pure r, c, c, ?_, rfl, fun b => b.elim⟩
      simp only [mapSpecStep, shape', h]
      congr 1
      funext b; exact b.elim
  | step =>
      refine ⟨.step, c, c, ?_, rfl, fun _ => rfl⟩
      simp only [mapSpecStep, shape', h]
  | query a =>
      refine ⟨.query a, c, c, ?_, rfl, fun _ => rfl⟩
      show mapSpecStep (PFunctor.Lens.id E) u = ⟨.query a, c⟩
      simp only [mapSpecStep, shape', h]
      rfl

/-- Computing one `M.dest` step of `mapSpec`, in terms of `mapSpecStep`. -/
theorem dest_mapSpec (φ : PFunctor.Lens E F) (u : ITree E α) :
    PFunctor.M.dest (mapSpec φ u) =
      ⟨(mapSpecStep φ u).1, fun b => mapSpec φ ((mapSpecStep φ u).2 b)⟩ := by
  rw [mapSpec, PFunctor.M.dest_corec_apply]

/-- Same as `dest_mapSpec` but stated with `shape'` on the LHS. -/
theorem shape'_mapSpec (φ : PFunctor.Lens E F) (u : ITree E α) :
    shape' (mapSpec φ u) =
      ⟨(mapSpecStep φ u).1, fun b => mapSpec φ ((mapSpecStep φ u).2 b)⟩ :=
  dest_mapSpec φ u

theorem mapSpec_comp (φ : PFunctor.Lens E F) (ψ : PFunctor.Lens F G) (t : ITree E α) :
    mapSpec (ψ ∘ₗ φ) t = mapSpec ψ (mapSpec φ t) := by
  refine PFunctor.M.corec_eq_corec
    (mapSpecStep (ψ ∘ₗ φ)) (mapSpecStep ψ)
    (fun u v => v = mapSpec φ u) t (mapSpec φ t) rfl ?_
  rintro u v rfl
  rcases h : PFunctor.M.dest u with ⟨sh, c⟩
  have hu : shape' u = ⟨sh, c⟩ := h
  cases sh with
  | pure r =>
      refine ⟨.pure r, PEmpty.elim, PEmpty.elim, ?_, ?_, ?_⟩
      · show mapSpecStep (ψ ∘ₗ φ) u = ⟨.pure r, PEmpty.elim⟩
        rw [mapSpecStep, hu]
      · show mapSpecStep ψ (mapSpec φ u) = ⟨.pure r, PEmpty.elim⟩
        rw [mapSpecStep, shape'_mapSpec, mapSpecStep, hu]
      · intro b; exact b.elim
  | step =>
      refine ⟨.step, fun _ => c PUnit.unit, fun _ => mapSpec φ (c PUnit.unit),
        ?_, ?_, fun _ => rfl⟩
      · show mapSpecStep (ψ ∘ₗ φ) u = ⟨.step, fun _ => c PUnit.unit⟩
        rw [mapSpecStep, hu]
      · show mapSpecStep ψ (mapSpec φ u) = ⟨.step, fun _ => mapSpec φ (c PUnit.unit)⟩
        rw [mapSpecStep, shape'_mapSpec, mapSpecStep, hu]
  | query a =>
      refine ⟨.query (ψ.toFunA (φ.toFunA a)),
        fun b => c ((ψ ∘ₗ φ).toFunB a b),
        fun b => mapSpec φ (c ((ψ ∘ₗ φ).toFunB a b)),
        ?_, ?_, fun _ => rfl⟩
      · show mapSpecStep (ψ ∘ₗ φ) u =
          ⟨.query (ψ.toFunA (φ.toFunA a)), fun b => c ((ψ ∘ₗ φ).toFunB a b)⟩
        rw [mapSpecStep, hu]
        rfl
      · show mapSpecStep ψ (mapSpec φ u) =
          ⟨.query (ψ.toFunA (φ.toFunA a)),
            fun b => mapSpec φ (c ((ψ ∘ₗ φ).toFunB a b))⟩
        rw [mapSpecStep, shape'_mapSpec, mapSpecStep, hu]
        rfl

/-! ### Relating `simulate` and `mapSpec` -/

theorem simulate_ofLens (φ : PFunctor.Lens E F) (t : ITree E α) :
    WeakBisim (simulate (Handler.ofLens φ) t) (mapSpec φ t) := by
  sorry

end ITree
