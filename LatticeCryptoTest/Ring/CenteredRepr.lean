/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import LatticeCrypto.Ring.Norms
import Mathlib.Tactic.ReduceModChar

/-!
# Gate for the centered representative and modular numerals

`centeredRepr` is `ZMod.valMinAbs` under the FIPS-facing name, so Mathlib's `valMinAbs` API
applies to it directly: closed values by `decide`, the absolute value as a `min` through
`ZMod.valMinAbs_natAbs_eq_min`, and casts of small naturals by `valMinAbs_natCast_of_le_half`.
Numeral identities in `ZMod q` for a literal `q` close by `reduce_mod_char`.
-/

public section

open LatticeCrypto

namespace LatticeCryptoTest.CenteredRepr

example : centeredRepr (12 : ZMod 17) = -5 := by decide
example : centeredRepr (3 : ZMod 17) = 3 := by decide

example : (centeredRepr (12 : ZMod 17)).natAbs = 5 := by
  rw [centeredRepr_eq_valMinAbs, ZMod.valMinAbs_natAbs_eq_min]
  decide

example (a : ℕ) (h : a ≤ 17 / 2) : centeredRepr (a : ZMod 17) = a :=
  ZMod.valMinAbs_natCast_of_le_half h

example (x : ZMod 17) : (centeredRepr x).natAbs ≤ 8 := centeredRepr_abs_le x

example : ((8380416 : ℕ) : ZMod 8380417) = -1 := by reduce_mod_char
example : (1753 : ZMod 8380417) ^ 256 = -1 := by reduce_mod_char
example : (17 : ZMod 3329) ^ 128 = -1 := by reduce_mod_char

end LatticeCryptoTest.CenteredRepr
