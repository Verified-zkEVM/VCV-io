/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import ToMathlib.Control.WriterT

/-!
# `Std.Do` weakest-precondition bridge for `WriterT`

Provides `Std.Do.WP` and `Std.Do.WPMonad` instances for `WriterT ω m`,
together with `@[spec]` lemmas for `MonadWriter.tell`,
`MonadLift.monadLift`, and `WriterT.run`. With these in scope, `mvcgen`
can walk through any `do`-block in `WriterT ω m`, treating the writer
log `ω` as a state component (post-shape `(.arg ω ps)` where `ps` is the
inner monad's post-shape).

The bridge supports the `[EmptyCollection ω] [Append ω] [LawfulAppend ω]`
parameterization, which is what `loggingOracle` (over
`WriterT (QueryLog spec) (OracleComp spec)`) needs because `QueryLog spec`
unfolds to `List _`. The dual `[Monoid ω]` parameterization can be added
in the same shape if and when needed.

## Implementation

`wp x` for `x : WriterT ω m α` is interpreted as the state-tracking
predicate transformer
```
PredTrans.pushArg (fun (s : ω) =>
  (fun z : α × ω => (z.1, s ++ z.2)) <$> wp (WriterT.run x))
```
i.e., the writer log is threaded through as state and accumulated via
`++`. The `LawfulAppend` law (`empty_append`, `append_empty`,
`append_assoc`) is what makes `wp` preserve `pure` and `bind`.
-/

open Std.Do

universe u v

namespace WriterT

/-! ## `Append`-based `WP` interpretation -/

/-- The underlying predicate-transformer interpretation of a `WriterT ω m`
computation, factored out so that the `WP` instance and the proofs
defining `WPMonad` can refer to it by a single name. The writer log is
threaded through as state and accumulated via `++`. -/
def wpAppend {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}} {α : Type u}
    [Monad m] [WP m ps] [EmptyCollection ω] [Append ω]
    (x : WriterT ω m α) : PredTrans (.arg ω ps) α :=
  PredTrans.pushArg (fun (s : ω) =>
    (fun (z : α × ω) => (z.1, s ++ z.2)) <$> wp (WriterT.run x))

/-- Weakest-precondition interpretation of `WriterT ω m` as a state-tracking
predicate transformer over the writer log `ω`, with post-shape
`(.arg ω ps)`. The log is accumulated via `++` with identity `∅`.

This instance only needs the writer combinators `EmptyCollection` and
`Append` to be definable; lawfulness (`LawfulAppend`) is required for the
`WPMonad` extension. -/
instance instWPAppend {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}}
    [Monad m] [WP m ps] [EmptyCollection ω] [Append ω] :
    WP (WriterT ω m) (.arg ω ps) where
  wp x := WriterT.wpAppend x

/-- `WP` for `WriterT ω m` is a monad morphism: it preserves `pure` and
`bind`. Requires `LawfulAppend ω` (so `s ++ ∅ = s` and `++` is associative)
and lawfulness of the inner monad. -/
instance instWPMonadAppend {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}}
    [Monad m] [LawfulMonad m] [WPMonad m ps]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] :
    WPMonad (WriterT ω m) (.arg ω ps) where
  toLawfulMonad := inferInstance
  toWP := instWPAppend
  wp_pure {α} a := by
    apply PredTrans.ext
    intro Q
    change (WriterT.wpAppend (pure a : WriterT ω m α)).apply Q
        = (Pure.pure a : PredTrans (.arg ω ps) α).apply Q
    simp only [WriterT.wpAppend, WriterT.run_pure', WPMonad.wp_pure,
      PredTrans.apply_pushArg, PredTrans.apply_Functor_map,
      PredTrans.apply_Pure_pure, LawfulAppend.append_empty]
  wp_bind {α β} x f := by
    apply PredTrans.ext
    intro Q
    change (WriterT.wpAppend (x >>= f)).apply Q
        = ((WriterT.wpAppend x : PredTrans (.arg ω ps) α) >>=
            fun a => WriterT.wpAppend (f a)).apply Q
    simp only [WriterT.wpAppend, WriterT.run_bind', WPMonad.wp_bind,
      WPMonad.wp_map, PredTrans.apply_pushArg,
      PredTrans.apply_Functor_map, PredTrans.apply_Bind_bind,
      Prod.map_fst, Prod.map_snd, id_eq]
    funext s
    congr 1
    refine Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩
    funext aw
    congr 1
    refine Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩
    funext z
    rw [LawfulAppend.append_assoc]

end WriterT

/-! ## `wp` simp lemmas for `WriterT` operations

These rewrite `wp⟦x⟧ Q` for common `WriterT` operations (`tell`,
`monadLift`) into simpler forms involving the inner monad's `wp`. They are
analogous to `Std.Do.WP.monadLift_StateT`, etc. -/

namespace Std.Do.WP

@[simp]
theorem tell_WriterT {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}}
    [Monad m] [LawfulMonad m] [WPMonad m ps]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (w : ω) (Q : PostCond PUnit (.arg ω ps)) :
    wp⟦MonadWriter.tell w : WriterT ω m PUnit⟧ Q = fun s => Q.1 ⟨⟩ (s ++ w) := by
  simp only [WP.wp, WriterT.wpAppend, WriterT.run_tell, WPMonad.wp_pure,
    PredTrans.apply_pushArg, PredTrans.apply_Functor_map,
    PredTrans.apply_Pure_pure]

@[simp]
theorem monadLift_WriterT {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}}
    {α : Type u}
    [Monad m] [LawfulMonad m] [WPMonad m ps]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (x : m α) (Q : PostCond α (.arg ω ps)) :
    wp⟦MonadLift.monadLift x : WriterT ω m α⟧ Q
        = fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2) := by
  simp only [WP.wp, WriterT.wpAppend, MonadLift.monadLift,
    WriterT.run_mk, WPMonad.wp_map,
    PredTrans.apply_pushArg, PredTrans.apply_Functor_map,
    LawfulAppend.append_empty]

end Std.Do.WP

/-! ## `@[spec]` lemmas

The following spec lemmas register `WriterT ω m` operations with
`mvcgen`'s discrimination tree, so that `mvcgen` can walk through
`do`-blocks involving `tell`, `monadLift`, and the underlying `run`
projection. -/

namespace Std.Do.Spec

attribute [spec] WriterT.run

/-- Spec for `MonadWriter.tell` in `WriterT ω m`. The precondition is
`Q.1 ⟨⟩ (s ++ w)`, i.e., the postcondition holds for `()` with the new
state being the old state appended with the written value `w`. -/
@[spec]
theorem tell_WriterT {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}}
    [Monad m] [LawfulMonad m] [WPMonad m ps]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (w : ω) {Q : PostCond PUnit (.arg ω ps)} :
    Triple (m := WriterT ω m) (MonadWriter.tell w)
      (spred(fun s => Q.1 ⟨⟩ (s ++ w)))
      Q := by
  simp [Triple.iff, SPred.entails.refl]

/-- Spec for `MonadLift.monadLift` from `m` to `WriterT ω m`. The lifted
computation `x : m α` runs in the inner monad with the writer state
unchanged (since the lift writes `∅` and `s ++ ∅ = s`). -/
@[spec]
theorem monadLift_WriterT {m : Type u → Type v} {ω : Type u} {ps : PostShape.{u}}
    {α : Type u}
    [Monad m] [LawfulMonad m] [WPMonad m ps]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (x : m α) {Q : PostCond α (.arg ω ps)} :
    Triple (m := WriterT ω m) (MonadLift.monadLift x)
      (spred(fun s => wp⟦x⟧ (fun a => Q.1 a s, Q.2)))
      Q := by
  simp [Triple.iff, SPred.entails.refl]

end Std.Do.Spec
