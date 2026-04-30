import Loom.WP.Basic
import Loom.Lawful.Lift

open Lean.Order Loom

variable (m : Type u₁ → Type u₂) (Pred : Type u₁) (EPred : Type u₁) [Monad m] [WP m Pred EPred]

class LawfulMonadStateOf (σ : Type u₁) [WP m Pred EPred]
  [MonadStateOf σ m] [MonadStateOf σ (PredTrans Pred EPred)] where
  wp_get : (get : PredTrans Pred EPred σ) ⊑ wp (get : m σ)
  wp_set (s : σ) : (set s : PredTrans Pred EPred PUnit) ⊑ wp (set s : m PUnit)
  wp_modifyGet (f : σ → α × σ) : (modifyGet f : PredTrans Pred EPred α) ⊑ wp (modifyGet f : m α)

instance StateT.instLawfulMonadStateOf (σ : Type u₁) : LawfulMonadStateOf (StateT σ m) (σ → Pred) EPred σ where
  wp_get := by
    simp [get, getThe, MonadStateOf.get]
    intro post epost s
    unfold wp; simp [WP.wpTrans]
    unfold StateT.get StateT.run; simp; apply PartialOrder.rel_trans; rotate_left;
    apply WP.wp_pure; rfl
  wp_set := by
    simp [set, MonadStateOf.set]
    intro post epost e s
    unfold wp; simp [WP.wpTrans]
    unfold StateT.set StateT.run; simp; apply PartialOrder.rel_trans; rotate_left;
    apply WP.wp_pure; rfl
  wp_modifyGet := by
    simp [modifyGet, MonadStateOf.modifyGet]
    intro α post post' epost s; simp
    unfold wp StateT.modifyGet StateT.run; simp; apply PartialOrder.rel_trans; rotate_left;
    apply WP.wp_pure; rfl

instance (σ ε : Type u₁)
  [MonadStateOf σ m] [MonadStateOf σ (PredTrans Pred EPred)] [LawfulMonadStateOf m Pred EPred σ] :
  LawfulMonadStateOf (ExceptT ε m) Pred (EPost.cons (ε → Pred) EPred) σ where
  wp_get := by sorry
  wp_set := by sorry
  wp_modifyGet := by sorry

instance (σ σ' : Type u₁)
  [MonadStateOf σ m] [MonadStateOf σ (PredTrans Pred EPred)] [LawfulMonadStateOf m Pred EPred σ] :
  LawfulMonadStateOf (StateT σ' m) (σ' → Pred) EPred σ where
  wp_get := by sorry
  wp_set := by sorry
  wp_modifyGet := by sorry

instance (σ ρ : Type u₁)
  [MonadStateOf σ m] [MonadStateOf σ (PredTrans Pred EPred)] [LawfulMonadStateOf m Pred EPred σ] :
  LawfulMonadStateOf (ReaderT ρ m) (ρ → Pred) EPred σ where
  wp_get := by sorry
  wp_set := by sorry
  wp_modifyGet := by sorry

-- instance (σ : Type u₁)
--   [MonadStateOf σ m] [MonadStateOf σ (PredTrans Pred EPred)] [LawfulMonadStateOf m Pred EPred σ]
--   (n : Type u₁ → Type u₂) (k : Type u₁) (d : Type u₁)
--   [CompleteLattice k] [CompleteLattice d] [Monad n] [WP n k d]
--   [MonadLift m n]
--   [MonadLift (PredTrans Pred EPred) (PredTrans k d)]
--   [LawfulWPLift m Pred EPred n k d] :
--   LawfulMonadStateOf n k d σ where
--   wp_get := by
--     simp [get, getThe, MonadStateOf.get]
--     apply PartialOrder.rel_trans; rotate_left
--     apply LawfulWPLift.lift_wp_trans (Pred := Pred) (EPred := EPred)
--     apply LawfulWPLift.lift_monotone (m := m) (n := n)
--     apply LawfulMonadStateOf.wp_get
--   wp_set := by
--     simp [set, MonadStateOf.set]; intro s
--     apply PartialOrder.rel_trans; rotate_left
--     apply LawfulWPLift.lift_wp_trans (Pred := Pred) (EPred := EPred)
--     apply LawfulWPLift.lift_monotone (m := m) (n := n)
--     apply LawfulMonadStateOf.wp_set
--   wp_modifyGet := by
--     simp [modifyGet, MonadStateOf.modifyGet]; intro α f
--     apply PartialOrder.rel_trans; rotate_left
--     apply LawfulWPLift.lift_wp_trans (Pred := Pred) (EPred := EPred)
--     apply lift_monotone (m := m) (n := n)
--     apply LawfulMonadStateOf.wp_modifyGet


class LawfulMonadReaderOf (ρ : Type u₁) [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans Pred EPred)] where
  wp_read : (read : PredTrans Pred EPred ρ) ⊑ wp (read : m ρ)

instance (ρ : Type u₁) : LawfulMonadReaderOf (ReaderT ρ m) (ρ → Pred) EPred ρ where
  wp_read := by
    simp [read, readThe, MonadReaderOf.read]
    intro post epost r
    unfold wp; simp [WP.wpTrans]
    apply PartialOrder.rel_trans; rotate_left;
    apply WP.wp_pure; rfl

instance (ρ ρ' : Type u₁)
  [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans Pred EPred)] [LawfulMonadReaderOf m Pred EPred ρ] :
  LawfulMonadReaderOf (ReaderT ρ' m) (ρ' → Pred) EPred ρ where
  wp_read := by sorry

instance (ρ ε : Type u₁)
  [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans Pred EPred)] [LawfulMonadReaderOf m Pred EPred ρ] :
  LawfulMonadReaderOf (ExceptT ε m) Pred (EPost.cons (ε → Pred) EPred) ρ where
  wp_read := by sorry

instance (ρ σ : Type u₁)
  [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans Pred EPred)] [LawfulMonadReaderOf m Pred EPred ρ] :
  LawfulMonadReaderOf (StateT σ m) (σ → Pred) EPred ρ where
  wp_read := by sorry

-- instance (ρ : Type u₁)
--   [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans Pred EPred)] [LawfulMonadReaderOf m Pred EPred ρ]
--   (n : Type u₁ → Type u₂) (k : Type u₁) (d : Type u₁)
--   [CompleteLattice k] [CompleteLattice d] [Monad n] [WP n k d]
--   [MonadLift m n]
--   [MonadLift (PredTrans Pred EPred) (PredTrans k d)]
--   [LawfulWPLiftT m Pred EPred n k d] :
--   LawfulMonadReaderOf n k d ρ where
--   wp_read := by
--     simp [read, readThe, MonadReaderOf.read]
--     apply PartialOrder.rel_trans; rotate_left
--     apply lift_wp_trans (Pred := Pred) (EPred := EPred)
--     apply lift_monotone (m := m) (n := n)
--     apply LawfulMonadReaderOf.wp_read
