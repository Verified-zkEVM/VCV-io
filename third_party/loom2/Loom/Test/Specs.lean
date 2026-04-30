import Loom.Triple.SpecLemmas

namespace Loom

open Lean.Order Std.Do' WP

universe u v

@[lspec]
theorem Spec.MonadState_get_StateT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    Triple (fun s => post s s) (get (m := StateT σ m)) post epost := by
  simpa using (Spec.get_StateT (m := m) (Pred := Pred) (EPred := EPred) (σ := σ) (epost := epost) post)

@[lspec]
theorem Spec.MonadState_set_StateT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {σ : Type u} {s : σ} (post : PUnit → σ → Pred) (epost : EPred) :
    Triple (fun _ => post ⟨⟩ s) (set (m := StateT σ m) s) post epost := by
  apply Spec.set_StateT (m := m) (Pred := Pred) (EPred := EPred) (σ := σ) (epost := epost)

@[lspec]
theorem Spec.MonadState_get_ExceptT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {ε : Type u} (post : σ → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (get : m σ)) post epost)
      (get : ExceptT ε m σ) post epost := by
  apply Triple.iff.mpr
  simpa [get_MonadState_wp, get_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl : wp (get : ExceptT ε m σ) post epost ⊑ wp (get : ExceptT ε m σ) post epost)

@[lspec]
theorem Spec.MonadStateOf_get_ReaderT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {ρ : Type u} (post : σ → ρ → Pred) (epost : EPred) :
    Triple (wp (MonadLift.monadLift (n := ReaderT ρ m) (get : m σ)) post epost)
      (MonadStateOf.get : ReaderT ρ m σ) post epost := by
  apply Triple.iff.mpr
  simpa [get_MonadState_wp, get_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl : wp (get : ReaderT ρ m σ) post epost ⊑ wp (get : ReaderT ρ m σ) post epost)

@[lspec]
theorem Spec.MonadStateOf_get_ExceptT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {ε : Type u} (post : σ → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (MonadStateOf.get : m σ)) post epost)
      (MonadStateOf.get : ExceptT ε m σ) post epost := by
  apply Triple.iff.mpr
  simpa [get_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl :
      wp (MonadStateOf.get : ExceptT ε m σ) post epost ⊑ wp (MonadStateOf.get : ExceptT ε m σ) post epost)

@[lspec]
theorem Spec.MonadStateOf_get_StateT_lift
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {σ' : Type u} (post : σ → σ' → Pred) (epost : EPred) :
    Triple (wp (MonadLift.monadLift (n := StateT σ' m) (get : m σ)) post epost)
      (MonadStateOf.get (σ := σ) : StateT σ' m σ) post epost := by
  apply Triple.iff.mpr
  simpa [get_MonadState_wp, get_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl :
      wp (MonadStateOf.get (σ := σ) : StateT σ' m σ) post epost
        ⊑ wp (MonadStateOf.get (σ := σ) : StateT σ' m σ) post epost)

@[lspec]
theorem Spec.MonadStateOf_set_ExceptT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {ε : Type u} {s : σ} (post : PUnit → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (set (m := m) s)) post epost)
      (set (m := ExceptT ε m) s) post epost := by
  apply Triple.iff.mpr
  simpa [set_MonadState_wp, set_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl :
      wp (set (m := ExceptT ε m) s) post epost ⊑ wp (set (m := ExceptT ε m) s) post epost)

@[lspec]
theorem Spec.MonadStateOf_set_ReaderT
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {ρ : Type u} {s : σ} (post : PUnit → ρ → Pred) (epost : EPred) :
    Triple (wp (MonadLift.monadLift (n := ReaderT ρ m) (set (m := m) s)) post epost)
      (set (m := ReaderT ρ m) s) post epost := by
  apply Triple.iff.mpr
  simpa [set_MonadState_wp, set_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl : wp (set (m := ReaderT ρ m) s) post epost ⊑ wp (set (m := ReaderT ρ m) s) post epost)

@[lspec]
theorem Spec.MonadStateOf_set_StateT_lift
    {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {σ' : Type u} {s : σ} (post : PUnit → σ' → Pred) (epost : EPred) :
    Triple (wp (MonadLift.monadLift (n := StateT σ' m) (set (m := m) s)) post epost)
      (set (m := StateT σ' m) s) post epost := by
  apply Triple.iff.mpr
  simpa [set_MonadState_wp, set_MonadStateOf_lift_wp] using
    (PartialOrder.rel_refl :
      wp (set (m := StateT σ' m) s) post epost ⊑ wp (set (m := StateT σ' m) s) post epost)

end Loom
