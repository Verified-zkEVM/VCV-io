/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Bisim.Equiv

/-! # Algebraic laws for `bind` and `iter`

The classical equational theory of interaction trees, lifted to Lean. All
laws are stated either as strong bisimulations (`Bisim`, i.e. definitional
equality of M-types) or weak bisimulations (`WeakBisim`).

## Main statements

* `bind_pure_left`, `bind_pure_right`, `bind_assoc` — monad laws on
  `ITree.bind`. The first two are strong bisimulations via `M.bisim`; the
  third likewise.
* `iter_unfold` — the canonical fixed-point equation for `ITree.iter`,
  matching the Coq `unfold_iter` (`Core/ITreeDefinition.v`).
* `iter_bind` — left-distributive interaction between `iter` and `bind`.
* `step_weakBisim` — silent steps are absorbed by weak bisimulation
  (`step t ≈ t`); the defining feature of `eutt`.

The proofs are scaffolded with `sorry`. The strong-bisimulation laws
(`bind_pure_left`, `bind_pure_right`, `bind_assoc`) reduce to constructing
explicit `PFunctor.M`-bisimulations and discharging them with
`PFunctor.M.bisim`. The weak-bisimulation laws (`iter_unfold`, `iter_bind`,
`step_weakBisim`) require the project's coinductive proof tooling, which is
under active development.
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
private theorem dest_bind_step (k : α → ITree F β) (t : ITree F α)
    (c : PUnit → ITree F α) (h : PFunctor.M.dest t = ⟨.step, c⟩) :
    PFunctor.M.dest (bind t k) = ⟨.step, fun _ => bind (c PUnit.unit) k⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  rfl

/-- Compute one `M.dest` step of `bind` whose head is a query. -/
private theorem dest_bind_query (k : α → ITree F β) (t : ITree F α) (a : F.A)
    (c : F.B a → ITree F α) (h : PFunctor.M.dest t = ⟨.query a, c⟩) :
    PFunctor.M.dest (bind t k) = ⟨.query a, fun b => bind (c b) k⟩ := by
  rw [bind, PFunctor.M.dest_corec_apply, bindStep_inl, h]
  rfl

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

theorem iter_bind (body : β → ITree F (β ⊕ α)) (k : α → ITree F γ) (init : β) :
    bind (iter body init) k =
      iter (fun b => bind (body b) (fun rj => match rj with
        | .inl j => pure (.inl j)
        | .inr r => bind (k r) (fun c => pure (.inr c)))) init := by
  sorry

/-! ### Step is weakly absorbed -/

theorem step_weakBisim (t : ITree F α) : WeakBisim (step t) t :=
  WeakBisim.tauL (step t) t t (shape'_step _) (WeakBisim.refl t)

end ITree
