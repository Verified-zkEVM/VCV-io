/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Distribution Semantics for Computations with Bit Vectors

This file contains lemmas for `probEvent` and `probOutput` of computations involving `BitVec`.
-/

namespace OracleComp

open OracleSpec BitVec

variable {ι : Type} {spec : OracleSpec ι} {α β γ : Type}

@[simp]
lemma probOutput_bitVec_ofFin_map {n : ℕ} (oa : OracleComp spec (Fin (2 ^ n)))
    (x : BitVec n) : [= x | ofFin <$> oa] = [= toFin x | oa] :=
  probOutput_map_eq_probOutput_inverse oa ofFin toFin (congrFun rfl) (congrFun rfl) x

@[simp]
lemma probOutput_bitVec_toFin_map {n : ℕ} (oa : OracleComp spec (BitVec n))
    (x : Fin (2 ^ n)) : [= x | toFin <$> oa] = [= ofFin x | oa] :=
  probOutput_map_eq_probOutput_inverse oa toFin ofFin (congrFun rfl) (congrFun rfl) x

/-- Choose a random bit-vector by converting a random number in number between `0` and `2 ^ n`-/
instance (n : ℕ) : SelectableType (BitVec n) where
  selectElem := ofFin <$> ($ᵗ Fin (2 ^ n))
  probOutput_selectElem_eq x y := by simp only [probOutput_bitVec_ofFin_map,
    probOutput_uniformOfFintype, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  probFailure_selectElem := by simp

end OracleComp
