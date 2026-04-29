/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import ToMathlib.ITree.Bisim.Equiv

/-! # Algebraic laws for `bind` and `iter`

The classical equational theory of interaction trees, lifted to Lean. All
laws are stated either as strong bisimulations (`Bisim`, i.e. definitional
equality of M-types) or weak bisimulations (`WeakBisim`).

## Main statements

* `bind_pure_left`, `bind_pure_right`, `bind_assoc` — monad laws on
  `ITree.bind`, as strong bisimulations (i.e. definitional equalities on
  `PFunctor.M`).
* `bind_step`, `bind_query` — `bind` distributes over a leading silent
  step / visible query.
* `iter_unfold` — the canonical fixed-point equation for `ITree.iter`,
  matching the Coq `unfold_iter` (`Core/ITreeDefinition.v`).
* `iter_bind` — left-distributive interaction between `iter` and `bind`.
* `step_weakBisim` — silent steps are absorbed by weak bisimulation
  (`step t ≈ t`); the defining feature of `eutt`.
* `bind_weakBisim_cont` — weak bind-congruence on the continuation.
-/

@[expose] public section

universe u

namespace ITree

variable {F : PFunctor.{u, u}} {α β γ : Type u}

/-! ### Monad laws -/

/-- Auxiliary: once `bind` has consumed the pure-leaf prefix and entered the
"already in `k r`" half of the corec state machine (`Sum.inr`), the corec is
the identity. -/
private theorem corec_bindStep_inr (k : α → ITree F β) (u : ITree F β) :
    PFunctor.M.corec (bindStep k) (Sum.inr u) = u := by
  refine PFunctor.M.bisim
    (fun a b => a = PFunctor.M.corec (bindStep k) (Sum.inr b)) ?_ _ _ rfl
  rintro a b rfl
  refine ⟨(PFunctor.M.dest b).1,
    fun i => PFunctor.M.corec (bindStep k) (Sum.inr ((PFunctor.M.dest b).2 i)),
    (PFunctor.M.dest b).2, ?_, rfl, fun i => rfl⟩
  rw [PFunctor.M.dest_corec_apply]
  rfl

theorem bind_pure_left (r : α) (k : α → ITree F β) :
    bind (pure r) k = k r := by
  apply PFunctor.M.eq_of_dest_eq
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl]
  change (match PFunctor.M.dest (k r) with
      | ⟨s, c⟩ => Sigma.mk s
          (fun b => PFunctor.M.corec (bindStep k) (Sum.inr (c b))) :
      (Poly F β).Obj (ITree F β)) = PFunctor.M.dest (k r)
  rcases hk : PFunctor.M.dest (k r) with ⟨sk, ck⟩
  change (Sigma.mk sk (fun b => PFunctor.M.corec (bindStep k) (Sum.inr (ck b))) :
      (Poly F β).Obj (ITree F β)) = ⟨sk, ck⟩
  congr 1
  funext b
  exact corec_bindStep_inr k (ck b)

theorem bind_pure_right (t : ITree F α) :
    bind t pure = t := by
  conv_rhs => rw [← PFunctor.M.corec_dest t]
  refine PFunctor.M.corec_eq_corec
    (bindStep (F := F) (pure : α → ITree F α)) PFunctor.M.dest
    (fun s u => s = Sum.inl u ∨ s = Sum.inr u) (Sum.inl t) t (Or.inl rfl) ?_
  rintro s u (rfl | rfl)
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    have hdest : PFunctor.M.dest u = ⟨sh, c⟩ := h
    cases sh with
    | pure r =>
        refine ⟨.pure r, PEmpty.elim, c, ?_, rfl, fun b => b.elim⟩
        unfold bindStep
        simp only [hdest]
        change (match shape' (pure r : ITree F α) with
            | ⟨s, c⟩ => Sigma.mk s (fun b => Sum.inr (c b)) :
            (Poly F α).Obj _) = ⟨.pure r, PEmpty.elim⟩
        rw [shape'_pure]
        change (Sigma.mk (.pure r) (fun b : PEmpty => Sum.inr (PEmpty.elim b)) :
            (Poly F α).Obj _) = ⟨.pure r, PEmpty.elim⟩
        congr 1
        funext b
        exact b.elim
    | step =>
        refine ⟨.step, fun _ => Sum.inl (c PUnit.unit), c, ?_, rfl,
                fun _ => Or.inl rfl⟩
        unfold bindStep
        simp only [hdest]
    | query a =>
        refine ⟨.query a, fun b => Sum.inl (c b), c, ?_, rfl,
                fun _ => Or.inl rfl⟩
        unfold bindStep
        simp only [hdest]
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    have hdest : PFunctor.M.dest u = ⟨sh, c⟩ := h
    refine ⟨sh, fun b => Sum.inr (c b), c, ?_, rfl, fun _ => Or.inr rfl⟩
    unfold bindStep
    simp only [hdest]

/-- Compute one `M.dest` step of `bind` whose head is a step. -/
theorem dest_bind_step (k : α → ITree F β) (t : ITree F α)
    (c : PUnit → ITree F α) (h : PFunctor.M.dest t = ⟨.step, c⟩) :
    PFunctor.M.dest (bind t k) = ⟨.step, fun _ => bind (c PUnit.unit) k⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  rfl

/-- Compute one `M.dest` step of `bind` whose head is a query. -/
theorem dest_bind_query (k : α → ITree F β) (t : ITree F α) (a : F.A)
    (c : F.B a → ITree F α) (h : PFunctor.M.dest t = ⟨.query a, c⟩) :
    PFunctor.M.dest (bind t k) = ⟨.query a, fun b => bind (c b) k⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  rfl

/-- `bind` distributes over a leading silent step. -/
theorem bind_step (t : ITree F α) (k : α → ITree F β) :
    bind (step t) k = step (bind t k) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [dest_bind_step k (step t) (fun _ => t) (shape'_step t),
      show PFunctor.M.dest (step (bind t k)) = ⟨.step, fun _ => bind t k⟩
        from shape'_step _]

/-- `bind` distributes over a leading query node. -/
theorem bind_query (a : F.A) (k : F.B a → ITree F α) (f : α → ITree F β) :
    bind (query a k) f = query a (fun b => bind (k b) f) := by
  apply PFunctor.M.eq_of_dest_eq
  rw [dest_bind_query f (query a k) a k (shape'_query a k),
      show PFunctor.M.dest (query a (fun b => bind (k b) f)) =
          ⟨.query a, fun b => bind (k b) f⟩ from shape'_query _ _]

theorem bind_assoc (t : ITree F α) (k : α → ITree F β) (k' : β → ITree F γ) :
    bind (bind t k) k' = bind t (fun a => bind (k a) k') := by
  refine PFunctor.M.bisim
    (fun (u v : ITree F γ) =>
      u = v ∨
      (∃ s : ITree F β, u = bind s k' ∧ v = bind s k') ∨
      ∃ t : ITree F α,
        u = bind (bind t k) k' ∧ v = bind t (fun a => bind (k a) k'))
    ?_ _ _ (Or.inr (Or.inr ⟨t, rfl, rfl⟩))
  rintro u v (rfl | ⟨s, rfl, rfl⟩ | ⟨t, rfl, rfl⟩)
  · -- u = v case: trivially bisimilar.
    rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · -- bind s k' on both sides: same destructor.
    rcases h : PFunctor.M.dest s with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have hs : s = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          change (⟨.pure r, c⟩ : (Poly F β).Obj _) = ⟨.pure r, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        clear h
        subst hs
        rw [bind_pure_left]
        rcases hk : PFunctor.M.dest (k' r) with ⟨sh', c'⟩
        exact ⟨sh', c', c', rfl, rfl, fun _ => Or.inl rfl⟩
    | step =>
        refine ⟨.step, fun _ => bind (c PUnit.unit) k',
          fun _ => bind (c PUnit.unit) k', ?_, ?_,
          fun _ => Or.inr (.inl ⟨_, rfl, rfl⟩)⟩
        · exact dest_bind_step k' s c h
        · exact dest_bind_step k' s c h
    | query a =>
        refine ⟨.query a, fun b => bind (c b) k', fun b => bind (c b) k',
          ?_, ?_, fun _ => Or.inr (.inl ⟨_, rfl, rfl⟩)⟩
        · exact dest_bind_query k' s a c h
        · exact dest_bind_query k' s a c h
  · -- the main "associativity" case.
    rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          change (⟨.pure r, c⟩ : (Poly F α).Obj _) = ⟨.pure r, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        clear h
        subst ht
        rw [bind_pure_left, bind_pure_left]
        rcases hkr : PFunctor.M.dest (bind (k r) k') with ⟨sh', c'⟩
        exact ⟨sh', c', c', rfl, rfl, fun _ => Or.inl rfl⟩
    | step =>
        have hbind : PFunctor.M.dest (bind t k) =
            ⟨.step, fun _ => bind (c PUnit.unit) k⟩ := dest_bind_step k t c h
        refine ⟨.step,
          fun _ => bind (bind (c PUnit.unit) k) k',
          fun _ => bind (c PUnit.unit) (fun a => bind (k a) k'),
          ?_, ?_, fun _ => Or.inr (.inr ⟨_, rfl, rfl⟩)⟩
        · exact dest_bind_step k' (bind t k) _ hbind
        · exact dest_bind_step (fun a => bind (k a) k') t c h
    | query a =>
        have hbind : PFunctor.M.dest (bind t k) =
            ⟨.query a, fun b => bind (c b) k⟩ := dest_bind_query k t a c h
        refine ⟨.query a,
          fun b => bind (bind (c b) k) k',
          fun b => bind (c b) (fun a => bind (k a) k'),
          ?_, ?_, fun _ => Or.inr (.inr ⟨_, rfl, rfl⟩)⟩
        · exact dest_bind_query k' (bind t k) a _ hbind
        · exact dest_bind_query (fun a => bind (k a) k') t a c h

/-! ### `iter` unfolding and interaction with `bind` -/

theorem iter_unfold (body : β → ITree F (β ⊕ α)) (init : β) :
    iter body init =
      bind (body init)
        (fun rj => match rj with
          | .inl j => step (iter body j)
          | .inr r => pure r) := by
  set kk : β ⊕ α → ITree F α := fun rj => match rj with
    | .inl j => step (iter body j)
    | .inr r => pure r with hkk
  refine PFunctor.M.bisim
    (fun (u v : ITree F α) =>
      u = v ∨ ∃ t : ITree F (β ⊕ α),
        u = PFunctor.M.corec (iterStep body) t ∧ v = bind t kk)
    ?_ _ _ (Or.inr ⟨body init, rfl, rfl⟩)
  rintro u v (rfl | ⟨t, rfl, rfl⟩)
  · -- u = v case.
    rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure rj =>
        cases rj with
        | inl j =>
            have ht : t = pure (.inl j) := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              change (⟨.pure (.inl j), c⟩ : (Poly F (β ⊕ α)).Obj _) =
                  ⟨.pure (.inl j), PEmpty.elim⟩
              congr 1; funext z; exact z.elim
            clear h
            subst ht
            refine ⟨.step, fun _ => iter body j, fun _ => iter body j,
              ?_, ?_, fun _ => Or.inl rfl⟩
            · -- M.dest (M.corec (iterStep body) (pure (.inl j))) = ⟨.step, _⟩
              rw [PFunctor.M.dest_corec_apply, iterStep,
                  show PFunctor.M.dest (pure (F := F) (.inl j : β ⊕ α)) =
                    ⟨.pure (.inl j), PEmpty.elim⟩ from PFunctor.M.dest_mk _]
              rfl
            · rw [bind_pure_left]
              show PFunctor.M.dest (kk (.inl j)) = ⟨.step, fun _ => iter body j⟩
              rw [hkk]
              exact shape'_step _
        | inr r =>
            have ht : t = pure (.inr r) := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              change (⟨.pure (.inr r), c⟩ : (Poly F (β ⊕ α)).Obj _) =
                  ⟨.pure (.inr r), PEmpty.elim⟩
              congr 1; funext z; exact z.elim
            clear h
            subst ht
            refine ⟨.pure r, PEmpty.elim, PEmpty.elim, ?_, ?_, fun b => b.elim⟩
            · rw [PFunctor.M.dest_corec_apply, iterStep,
                  show PFunctor.M.dest (pure (F := F) (.inr r : β ⊕ α)) =
                    ⟨.pure (.inr r), PEmpty.elim⟩ from PFunctor.M.dest_mk _]
              congr 1
              funext z
              exact z.elim
            · rw [bind_pure_left]
              show PFunctor.M.dest (kk (.inr r)) = ⟨.pure r, PEmpty.elim⟩
              rw [hkk]
              exact shape'_pure r
    | step =>
        refine ⟨.step,
          fun _ => PFunctor.M.corec (iterStep body) (c PUnit.unit),
          fun _ => bind (c PUnit.unit) kk,
          ?_, ?_, fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
        · rw [PFunctor.M.dest_corec_apply, iterStep, h]
        · exact dest_bind_step kk t c h
    | query a =>
        refine ⟨.query a,
          fun b => PFunctor.M.corec (iterStep body) (c b),
          fun b => bind (c b) kk,
          ?_, ?_, fun b => Or.inr ⟨c b, rfl, rfl⟩⟩
        · rw [PFunctor.M.dest_corec_apply, iterStep, h]
        · exact dest_bind_query kk t a c h

/-- Helper: `M.dest (bind u (fun c => pure (.inr c)))` when `u` has a pure head. -/
private theorem dest_bind_pureInr_of_pure (u : ITree F γ) (r : γ)
    (c_in : (Poly F γ).B (.pure r) → (Poly F γ).M)
    (h : PFunctor.M.dest u = ⟨.pure r, c_in⟩) :
    PFunctor.M.dest (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))) =
      ⟨.pure (.inr r), PEmpty.elim⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  change (match PFunctor.M.dest (pure (F := F) (.inr r : β ⊕ γ)) with
      | ⟨s, c'⟩ => Sigma.mk s
          (fun b => PFunctor.M.corec (bindStep (fun c : γ => pure (.inr c)))
            (.inr (c' b))) :
      (Poly F (β ⊕ γ)).Obj _) = _
  rw [show PFunctor.M.dest (pure (F := F) (.inr r : β ⊕ γ)) =
    ⟨.pure (.inr r), PEmpty.elim⟩ from PFunctor.M.dest_mk _]
  change (Sigma.mk (.pure (.inr r) : Shape F (β ⊕ γ))
    (fun b : PEmpty => PFunctor.M.corec
      (bindStep (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))
      (.inr (PEmpty.elim b))) : (Poly F (β ⊕ γ)).Obj _) = ⟨.pure (.inr r), PEmpty.elim⟩
  congr 1
  funext z
  exact z.elim

/-- Helper: `M.dest (bind u (fun c => pure (.inr c)))` when `u` has a step head. -/
private theorem dest_bind_pureInr_of_step (u : ITree F γ)
    (c : PUnit → ITree F γ) (h : PFunctor.M.dest u = ⟨.step, c⟩) :
    PFunctor.M.dest (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))) =
      ⟨.step, fun _ =>
        bind (c PUnit.unit) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  rfl

/-- Helper: `M.dest (bind u (fun c => pure (.inr c)))` when `u` has a query head. -/
private theorem dest_bind_pureInr_of_query (u : ITree F γ) (a : F.A)
    (c : F.B a → ITree F γ) (h : PFunctor.M.dest u = ⟨.query a, c⟩) :
    PFunctor.M.dest (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))) =
      ⟨.query a, fun b =>
        bind (c b) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  rfl

/-- Helper: `iterStep newBody (bind u (pure ∘ Sum.inr))` reduces to
`⟨.pure r, PEmpty.elim⟩` when `u` has a pure head carrying `r`. -/
private theorem iterStep_bind_pureInr_of_pure
    (newBody : β → ITree F (β ⊕ γ)) (u : ITree F γ) (r : γ)
    (c_in : (Poly F γ).B (.pure r) → (Poly F γ).M)
    (h : PFunctor.M.dest u = ⟨.pure r, c_in⟩) :
    iterStep newBody (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))) =
      ⟨.pure r, PEmpty.elim⟩ := by
  rw [iterStep, dest_bind_pureInr_of_pure u r c_in h]

/-- Helper: `iterStep newBody (bind u (pure ∘ Sum.inr))` reduces to
`⟨.step, _⟩` when `u` has a step head. -/
private theorem iterStep_bind_pureInr_of_step
    (newBody : β → ITree F (β ⊕ γ)) (u : ITree F γ)
    (c : PUnit → ITree F γ) (h : PFunctor.M.dest u = ⟨.step, c⟩) :
    iterStep newBody (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))) =
      ⟨.step, fun _ =>
        bind (c PUnit.unit) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))⟩ := by
  rw [iterStep, dest_bind_pureInr_of_step u c h]

/-- Helper: `iterStep newBody (bind u (pure ∘ Sum.inr))` reduces to
`⟨.query a, _⟩` when `u` has a query head. -/
private theorem iterStep_bind_pureInr_of_query
    (newBody : β → ITree F (β ⊕ γ)) (u : ITree F γ) (a : F.A)
    (c : F.B a → ITree F γ) (h : PFunctor.M.dest u = ⟨.query a, c⟩) :
    iterStep newBody (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))) =
      ⟨.query a, fun b =>
        bind (c b) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))⟩ := by
  rw [iterStep, dest_bind_pureInr_of_query u a c h]

/-- Helper: one `M.dest` step of `M.corec (iterStep newBody) (bind u wrapper_inr)`
when `u` has a pure head. -/
private theorem dest_corec_iter_bind_inr_of_pure
    (newBody : β → ITree F (β ⊕ γ)) (u : ITree F γ) (r : γ)
    (c_in : (Poly F γ).B (.pure r) → (Poly F γ).M)
    (h : PFunctor.M.dest u = ⟨.pure r, c_in⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep newBody)
        (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))) =
      ⟨.pure r, PEmpty.elim⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep_bind_pureInr_of_pure newBody u r c_in h]
  congr 1
  funext z
  exact z.elim

/-- Helper: one `M.dest` step of `M.corec (iterStep newBody) (bind u wrapper_inr)`
when `u` has a step head. -/
private theorem dest_corec_iter_bind_inr_of_step
    (newBody : β → ITree F (β ⊕ γ)) (u : ITree F γ)
    (c : PUnit → ITree F γ) (h : PFunctor.M.dest u = ⟨.step, c⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep newBody)
        (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))) =
      ⟨.step, fun _ => PFunctor.M.corec (iterStep newBody)
        (bind (c PUnit.unit) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep_bind_pureInr_of_step newBody u c h]

/-- Helper: one `M.dest` step of `M.corec (iterStep newBody) (bind u wrapper_inr)`
when `u` has a query head. -/
private theorem dest_corec_iter_bind_inr_of_query
    (newBody : β → ITree F (β ⊕ γ)) (u : ITree F γ) (a : F.A)
    (c : F.B a → ITree F γ) (h : PFunctor.M.dest u = ⟨.query a, c⟩) :
    PFunctor.M.dest (PFunctor.M.corec (iterStep newBody)
        (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))) =
      ⟨.query a, fun b => PFunctor.M.corec (iterStep newBody)
        (bind (c b) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))⟩ := by
  rw [PFunctor.M.dest_corec_apply, iterStep_bind_pureInr_of_query newBody u a c h]

theorem iter_bind (body : β → ITree F (β ⊕ α)) (k : α → ITree F γ) (init : β) :
    bind (iter body init) k =
      iter (fun b => bind (body b) (fun rj => match rj with
        | .inl j => pure (.inl j)
        | .inr r => bind (k r) (fun c => pure (.inr c)))) init := by
  set wrapper : β ⊕ α → ITree F (β ⊕ γ) := fun rj => match rj with
    | .inl j => pure (.inl j)
    | .inr r => bind (k r) (fun c => pure (.inr c)) with hwrapper
  set newBody : β → ITree F (β ⊕ γ) := fun b => bind (body b) wrapper with hnewBody
  change bind (PFunctor.M.corec (iterStep body) (body init)) k =
    PFunctor.M.corec (iterStep newBody) (newBody init)
  refine PFunctor.M.bisim
    (fun (lhs rhs : ITree F γ) =>
      (∃ t : ITree F (β ⊕ α),
        lhs = bind (PFunctor.M.corec (iterStep body) t) k ∧
        rhs = PFunctor.M.corec (iterStep newBody) (bind t wrapper)) ∨
      (∃ u : ITree F γ,
        lhs = u ∧
        rhs = PFunctor.M.corec (iterStep newBody)
          (bind u (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))))))
    ?_ _ _ (Or.inl ⟨body init, rfl, rfl⟩)
  rintro lhs rhs (⟨t, hlhs, hrhs⟩ | ⟨u, hlhs, hrhs⟩)
  · -- Phase A: running iter body wrapped in bind k.
    subst hlhs; subst hrhs
    rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure rj =>
        -- Promote `t` to literally `pure rj` via funext on `PEmpty`.
        have ht : t = pure rj := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          change (⟨.pure rj, c⟩ : (Poly F (β ⊕ α)).Obj _) = ⟨.pure rj, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        clear h
        subst ht
        rw [bind_pure_left]
        cases rj with
        | inl j =>
            -- RHS: wrapper (.inl j) = pure (.inl j).
            have hw : wrapper (.inl j) = (pure (.inl j) : ITree F (β ⊕ γ)) := by rw [hwrapper]
            rw [hw]
            -- Compute destructors: both sides have a step head.
            have hL : PFunctor.M.dest
                (PFunctor.M.corec (iterStep body) (pure (.inl j) : ITree F (β ⊕ α))) =
                ⟨.step, fun _ => PFunctor.M.corec (iterStep body) (body j)⟩ := by
              rw [PFunctor.M.dest_corec_apply, iterStep,
                show PFunctor.M.dest (pure (F := F) (.inl j : β ⊕ α)) =
                  ⟨.pure (.inl j), PEmpty.elim⟩ from PFunctor.M.dest_mk _]
            refine ⟨.step,
              fun _ => bind (PFunctor.M.corec (iterStep body) (body j)) k,
              fun _ => PFunctor.M.corec (iterStep newBody) (bind (body j) wrapper),
              ?_, ?_, fun _ => Or.inl ⟨body j, rfl, rfl⟩⟩
            · exact dest_bind_step k _ _ hL
            · rw [PFunctor.M.dest_corec_apply, iterStep,
                  show PFunctor.M.dest (pure (F := F) (.inl j : β ⊕ γ)) =
                    ⟨.pure (.inl j), PEmpty.elim⟩ from PFunctor.M.dest_mk _]
        | inr r =>
            -- RHS: wrapper (.inr r) = bind (k r) (pure ∘ inr).
            have hw : wrapper (.inr r) =
                bind (k r) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ))) := by
              rw [hwrapper]
            rw [hw]
            -- LHS: M.corec (iterStep body) (pure (.inr r)) is defeq to pure r (mod funext).
            have hcorec : PFunctor.M.corec (iterStep body) (pure (.inr r) : ITree F (β ⊕ α))
                = (pure r : ITree F α) := by
              apply PFunctor.M.eq_of_dest_eq
              rw [PFunctor.M.dest_corec_apply, iterStep,
                show PFunctor.M.dest (pure (F := F) (.inr r : β ⊕ α)) =
                  ⟨.pure (.inr r), PEmpty.elim⟩ from PFunctor.M.dest_mk _,
                show PFunctor.M.dest (pure (F := F) r) =
                  ⟨.pure r, PEmpty.elim⟩ from PFunctor.M.dest_mk _]
              change (⟨.pure r, fun b : PEmpty =>
                  PFunctor.M.corec (iterStep body) (PEmpty.elim b)⟩
                : (Poly F α).Obj _) = ⟨.pure r, PEmpty.elim⟩
              congr 1; funext z; exact z.elim
            rw [hcorec, bind_pure_left]
            -- Transition into Phase B with `u := k r`; case-split on `M.dest (k r)`.
            rcases hk : PFunctor.M.dest (k r) with ⟨sk, ck⟩
            cases sk with
            | pure r' =>
                refine ⟨.pure r', ck, PEmpty.elim, rfl, ?_, fun b => b.elim⟩
                exact dest_corec_iter_bind_inr_of_pure newBody (k r) r' ck hk
            | step =>
                refine ⟨.step, ck,
                  fun _ => PFunctor.M.corec (iterStep newBody)
                    (bind (ck PUnit.unit)
                      (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))),
                  rfl, ?_, fun _ => Or.inr ⟨ck PUnit.unit, rfl, rfl⟩⟩
                exact dest_corec_iter_bind_inr_of_step newBody (k r) ck hk
            | query a =>
                refine ⟨.query a, ck,
                  fun b => PFunctor.M.corec (iterStep newBody)
                    (bind (ck b) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))),
                  rfl, ?_, fun b => Or.inr ⟨ck b, rfl, rfl⟩⟩
                exact dest_corec_iter_bind_inr_of_query newBody (k r) a ck hk
    | step =>
        refine ⟨.step,
          fun _ => bind (PFunctor.M.corec (iterStep body) (c PUnit.unit)) k,
          fun _ => PFunctor.M.corec (iterStep newBody)
            (bind (c PUnit.unit) wrapper),
          ?_, ?_, fun _ => Or.inl ⟨c PUnit.unit, rfl, rfl⟩⟩
        · rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl,
              PFunctor.M.dest_corec_apply, iterStep, h]
          rfl
        · have hdest_bind : PFunctor.M.dest (bind t wrapper) =
              ⟨.step, fun _ => bind (c PUnit.unit) wrapper⟩ := dest_bind_step wrapper t c h
          rw [PFunctor.M.dest_corec_apply, iterStep, hdest_bind]
    | query a =>
        refine ⟨.query a,
          fun b => bind (PFunctor.M.corec (iterStep body) (c b)) k,
          fun b => PFunctor.M.corec (iterStep newBody) (bind (c b) wrapper),
          ?_, ?_, fun b => Or.inl ⟨c b, rfl, rfl⟩⟩
        · rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl,
              PFunctor.M.dest_corec_apply, iterStep, h]
          rfl
        · have hdest_bind : PFunctor.M.dest (bind t wrapper) =
              ⟨.query a, fun b => bind (c b) wrapper⟩ := dest_bind_query wrapper t a c h
          rw [PFunctor.M.dest_corec_apply, iterStep, hdest_bind]
  · -- Phase B: `k r` has been spliced in; rhs is running `bind lhs (pure ∘ inr)`.
    -- `rintro`'s substitution eliminated `u` in favor of `lhs`.
    subst hlhs; subst hrhs
    rcases h : PFunctor.M.dest lhs with ⟨sh, c⟩
    cases sh with
    | pure r =>
        refine ⟨.pure r, c, PEmpty.elim, rfl, ?_, fun b => b.elim⟩
        exact dest_corec_iter_bind_inr_of_pure newBody lhs r c h
    | step =>
        refine ⟨.step, c,
          fun _ => PFunctor.M.corec (iterStep newBody)
            (bind (c PUnit.unit) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))),
          rfl, ?_, fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
        exact dest_corec_iter_bind_inr_of_step newBody lhs c h
    | query a =>
        refine ⟨.query a, c,
          fun b => PFunctor.M.corec (iterStep newBody)
            (bind (c b) (fun c : γ => (pure (.inr c) : ITree F (β ⊕ γ)))),
          rfl, ?_, fun b => Or.inr ⟨c b, rfl, rfl⟩⟩
        exact dest_corec_iter_bind_inr_of_query newBody lhs a c h

/-! ### Step is weakly absorbed -/

/-- A leading silent step is weakly absorbed: `step t ≈ t`. -/
theorem step_weakBisim (t : ITree F α) : WeakBisim (step t) t :=
  WeakBisim.absorb_tauSteps_left
    (TauSteps.one (fun _ => t) (shape'_step t)) (WeakBisim.refl t)

/-! ### Weak bind-congruence on the continuation

Pointwise-weak-bisimilar continuations yield weakly-bisimilar `bind`s. This
is the `eutt` congruence lemma for `bind` on its second argument; the
standard tool for replacing a continuation up to weak equivalence. -/

/-- If `f a ≈ g a` for every `a`, then `bind u f ≈ bind u g`. -/
theorem bind_weakBisim_cont {u : ITree F α} {f g : α → ITree F β}
    (hfg : ∀ a, WeakBisim (f a) (g a)) :
    WeakBisim (bind u f) (bind u g) := by
  refine WeakBisim.coinduct
    (fun x y => (∃ u : ITree F α, x = bind u f ∧ y = bind u g) ∨ WeakBisim x y)
    ?_ (Or.inl ⟨u, rfl, rfl⟩)
  rintro a b (⟨u, rfl, rfl⟩ | hab)
  · rcases hu : PFunctor.M.dest u with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have hu_eq : u = pure r := by
          apply PFunctor.M.eq_of_dest_eq; rw [hu]
          change (⟨.pure r, c⟩ : (Poly F α).Obj _) = ⟨.pure r, PEmpty.elim⟩
          congr 1; funext z; exact z.elim
        subst hu_eq
        rw [bind_pure_left, bind_pure_left]
        obtain ⟨x', y', hx, hy, M⟩ := (hfg r).dest
        exact ⟨x', y', hx, hy, M.mono (fun _ _ hxy => Or.inr hxy)⟩
    | step =>
        refine ⟨bind u f, bind u g, .refl _, .refl _, ?_⟩
        refine Match.tau (fun _ => bind (c PUnit.unit) f)
          (fun _ => bind (c PUnit.unit) g) (dest_bind_step f u c hu)
          (dest_bind_step g u c hu) ?_
        exact Or.inl ⟨c PUnit.unit, rfl, rfl⟩
    | query a =>
        refine ⟨bind u f, bind u g, .refl _, .refl _, ?_⟩
        refine Match.query a (fun b => bind (c b) f) (fun b => bind (c b) g)
          (dest_bind_query f u a c hu) (dest_bind_query g u a c hu) ?_
        intro b
        exact Or.inl ⟨c b, rfl, rfl⟩
  · obtain ⟨x', y', hx, hy, M⟩ := hab.dest
    exact ⟨x', y', hx, hy, M.mono (fun _ _ hxy => Or.inr hxy)⟩

end ITree
