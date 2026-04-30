import Loom.WP.Basic
open Lean.Order Loom

section


section MonadLift

class LawfulWPLift
    (m : semiOutParam (Type u → Type v)) (Pred : semiOutParam (Type w)) (EPred : semiOutParam (Type z))
    (n : Type u → Type v') (k : Type w') (d : Type z')
    [Monad m] [WP m Pred EPred]
    [Monad n] [WP n k d]
    [inst : MonadLift m n] [inst' : MonadLift (PredTrans Pred EPred) (PredTrans k d)] : Prop where
  /-- Lifting preserves `wp` -/
  lift_wp_trans {α : Type u} (x : m α) : inst'.monadLift (wpTrans x) ⊑ wpTrans (inst.monadLift x)
  /-- Lifting is monotone -/
  lift_monotone {α : Type u} (x y : PredTrans Pred EPred α) :
    x ⊑ y → inst'.monadLift x ⊑ inst'.monadLift y


class LawfulWPLiftT
    (m : Type u → Type v) (Pred : Type w) (EPred : Type z)
    (n : Type u → Type v') (k : Type w') (d : Type z')
    [Monad m] [WP m Pred EPred]
    [Monad n] [WP n k d]
    [inst : MonadLiftT m n] [inst' : MonadLiftT (PredTrans Pred EPred) (PredTrans k d)] : Prop where
  /-- Lifting preserves `wp` -/
  lift_wp_trans {α : Type u} (x : m α) : inst'.monadLift (wpTrans x) ⊑ wpTrans (inst.monadLift x)
  /-- Lifting is monotone -/
  lift_monotone {α : Type u} (x y : PredTrans Pred EPred α) :
    x ⊑ y → inst'.monadLift x ⊑ inst'.monadLift y

export LawfulWPLiftT (lift_wp_trans lift_monotone)

instance (m : Type u → Type v) (Pred : Type w) (EPred : Type z) (σ : Type u)
  [Monad m] [WP m Pred EPred] :
  LawfulWPLift m Pred EPred (StateT σ m) (σ → Pred) EPred where
  lift_wp_trans x := fun post epost s => by
    simp only [MonadLift.monadLift]
    apply PartialOrder.rel_trans; rotate_left; apply WP.wp_bind
    apply WP.wp_consequence (m := m); intro a
    simpa using
      (WP.wp_pure (m := m) (x := (a, s))
        (post := fun x => post x.fst x.snd) (epost := epost))
  lift_monotone _ _ h := fun post epost s => h (fun a => post a s) epost

instance (m : Type u → Type v) (Pred : Type w) (EPred : Type z) (ρ : Type u)
  [Monad m] [WP m Pred EPred] :
  LawfulWPLift m Pred EPred (ReaderT ρ m) (ρ → Pred) EPred where
  lift_wp_trans _x := fun _post _epost _r => PartialOrder.rel_refl
  lift_monotone _ _ h := fun post epost r => h (fun a => post a r) epost

instance (m : Type u → Type v) (Pred : Type w) (EPred : Type z) (ε : Type u)
  [Monad m] [WP m Pred EPred] :
  LawfulWPLift m Pred EPred (ExceptT ε m) Pred (EPost.cons (ε → Pred) EPred) where
  lift_wp_trans x := fun post epost => by
    simp only [MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
    apply PartialOrder.rel_trans; rotate_left
    · exact WP.wp_map (m := m) Except.ok x _ _
    · exact PartialOrder.rel_refl
  lift_monotone _ _ h := fun post epost => h post epost.tail

variable {m : Type u → Type v} {n : Type u → Type w} {o : Type u → Type x}


-- analogue of instLawfulMonadLiftT (reflexive)
instance
    {Pred : Type w'} {EPred : Type z'}
    [Monad m] [WP m Pred EPred] :
    LawfulWPLiftT m Pred EPred m Pred EPred where
  lift_wp_trans _x := fun _post _epost => PartialOrder.rel_refl
  lift_monotone _ _ h := h

-- analogue of instLawfulMonadLiftTOfLawfulMonadLift (transitive)
instance
    {Pred : Type w'} {EPred : Type z'} {k : Type w''} {d : Type z''} {p : Type w'''} {c : Type z'''}
    [Monad m] [WP m Pred EPred]
    [Monad n] [WP n k d]
    [Monad o] [WP o p c]
    [MonadLiftT m n] [MonadLiftT (PredTrans Pred EPred) (PredTrans k d)]
    [MonadLift n o] [MonadLift (PredTrans k d) (PredTrans p c)]
    [LawfulWPLift n k d o p c] [LawfulWPLiftT m Pred EPred n k d] :
    LawfulWPLiftT m Pred EPred o p c where
  lift_wp_trans x := by
    apply PartialOrder.rel_trans
    · apply LawfulWPLift.lift_monotone (m := n) (n := o)
      exact LawfulWPLiftT.lift_wp_trans (n := n) x
    · exact LawfulWPLift.lift_wp_trans (monadLift x : n _)
  lift_monotone x y h := by
    apply LawfulWPLift.lift_monotone (m := n) (n := o)
    exact LawfulWPLiftT.lift_monotone (m := m) (n := n) (Pred := Pred) (EPred := EPred) (k := k) (d := d) x y h


end MonadLift
