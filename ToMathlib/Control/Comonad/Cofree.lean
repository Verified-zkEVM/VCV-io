/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Comonad.Basic
import Mathlib.Data.PFunctor.Univariate.M

/-! # Cofree Comonads

This file defines the `Cofree` comonad, which is a comonad that is constructed from a functor and a
coalgebra.

Since this is a coinductive type, the only way to define it right now is to use the `M` type
construction from `PFunctor`.

## Main definitions

* `CofreeC`: The `Cofree` comonad.
-/
