/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Tactic.Attr.Register

/-!
# `fs_simp` simp attribute for the stateful Fiat-Shamir CMA development

This file declares a single named simp set, `fs_simp`, used throughout the
stateful Fiat-Shamir CMA proof stack (everything under
`VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/`).

Tag handler definitions, frames, lenses, and adversary wrappers with
`@[fs_simp]` and use `simp [fs_simp, ...]` (or `simp only [fs_simp, ...]`) at
call sites instead of re-listing every recurring FS-CMA name on every
`unif/ro/sign/pk` × `none/some` leaf.

This attribute is intentionally **local** to the stateful FS-CMA development;
do not extend it with lemmas from outside `Sigma/Stateful/` or related
adversary helpers. The attribute is registered in its own file because
`register_simp_attr` does not take effect within the same Lean file as its
first use.
-/

/-- Simp set for unfolding stateful Fiat-Shamir CMA handlers, frames, lenses,
and adversary wrappers in one shot. Local to `Sigma/Stateful/`. -/
register_simp_attr fs_simp
