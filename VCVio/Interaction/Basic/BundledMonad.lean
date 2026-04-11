/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Bundled monads

`BundledMonad` packages a `Type u → Type v` constructor with a `Monad` instance so it can be
stored inside inductive types (e.g. per-node monad decorations) where typeclass inference is not
available. This module is independent of `Interaction.Spec`.
-/

universe u v

/-- Bundled monad: a monad constructor packaged as a structure for use inside `Spec` data. -/
structure BundledMonad where
  /-- The underlying monad family. -/
  M : Type u → Type v
  /-- Witness that `M` has a `Monad` instance. -/
  inst : Monad M

instance BundledMonad.instMonad (bm : BundledMonad) : Monad bm.M := bm.inst
