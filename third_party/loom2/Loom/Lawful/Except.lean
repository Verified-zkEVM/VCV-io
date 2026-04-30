import Loom.WP.Basic
import Loom.Lawful.Lift

open Lean.Order Loom

variable (m : Type u₁ → Type u₂) (Pred : Type u₁) (EPred : Type u₁) [Monad m] [WP m Pred EPred]


class LawfulMonadExceptOf (ε : Type u₁)
  [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans Pred EPred)] where
  wp_throw (err : ε) : (throw err : PredTrans Pred EPred α) ⊑ wp (throw err : m α)
  wp_tryCatch (x : m α) (h : ε → m α) : (tryCatch (wp x) (wp <| h ·) : PredTrans Pred EPred α) ⊑ wp (tryCatch x h)

instance (ε : Type u₁) : LawfulMonadExceptOf (ExceptT ε m) Pred (EPost.cons (ε → Pred) EPred) ε where
  wp_throw := by
    simp [throw, throwThe, MonadExceptOf.throw]
    intro α err post epost
    unfold wp; simp [WP.wpTrans]
    apply PartialOrder.rel_trans; rotate_left;
    apply WP.wp_pure; rfl
  wp_tryCatch := by
    intro α x h post epost
    simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
    unfold EPost.cons.pushExcept; simp
    simp [ExceptT.run, ExceptT.tryCatch, ExceptT.mk]
    apply PartialOrder.rel_trans; rotate_left;
    apply WP.wp_bind; apply WP.wp_consequence; intro r; cases r with
    | ok a =>
      simp; apply PartialOrder.rel_trans; rotate_left;
      apply WP.wp_pure; simp; rfl
    | error e => rfl

instance (ε ε' : Type u₁) [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans Pred EPred)] [LawfulMonadExceptOf m Pred EPred ε] :
  LawfulMonadExceptOf (ExceptT ε' m) Pred (EPost.cons (ε' → Pred) EPred) ε where
  wp_throw := by sorry
    -- simp [throw, throwThe, MonadExceptOf.throw]
    -- intro α err post epost
    -- unfold wp; simp [WP.wpTrans]
    -- apply LawfulMonadExceptOf.wp_throw (m := m)
  wp_tryCatch := by sorry
    -- intro α x h post epost
    -- simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
    -- apply PartialOrder.rel_trans; rotate_left;
    -- apply LawfulMonadExceptOf.wp_tryCatch
    -- simp [tryCatch, tryCatchThe]
    -- unfold EPost.cons.pushExcept; simp
    -- apply PartialOrder.rel_of_eq;
    -- repeat' apply congr <;> try rfl
    -- { funext; congr; grind }
    -- funext; congr; grind

instance (ε σ : Type u₁) [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans Pred EPred)] [LawfulMonadExceptOf m Pred EPred ε] :
  LawfulMonadExceptOf (StateT σ m) (σ → Pred) EPred ε where
  wp_throw := by sorry
  wp_tryCatch := by sorry

instance (ε ρ : Type u₁) [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans Pred EPred)] [LawfulMonadExceptOf m Pred EPred ε] :
  LawfulMonadExceptOf (ReaderT ρ m) (ρ → Pred) EPred ε where
  wp_throw := by sorry
  wp_tryCatch := by sorry
