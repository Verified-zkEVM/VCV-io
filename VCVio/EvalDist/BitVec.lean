/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Evaluation Distributions of Computations with `BitVec`

File for lemmas about `evalDist` and `support` involving `BitVec`.
-/

open BitVec OracleSpec OracleComp

variable {ι : Type _} {spec : OracleSpec ι} {α β γ : Type _}
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]

@[simp, grind =]
lemma probOutput_ofFin_map {n : ℕ} (mx : m (Fin (2 ^ n))) (x : BitVec n) :
    Pr[= x | ofFin <$> mx] = Pr[= toFin x | mx] := by aesop

@[simp, grind =]
lemma probOutput_bitVec_toFin_map {n : ℕ} (mx : m (BitVec n)) (x : Fin (2 ^ n)) :
    Pr[= x | toFin <$> mx] = Pr[= ofFin x | mx] := by aesop

-- /-- Choose a random bit-vector by converting a random number in number between `0` and `2 ^ n`-/
instance (n : ℕ) : SampleableType (BitVec n) where
  selectElem := ofFin <$> ($ᵗ Fin (2 ^ n))
  mem_support_selectElem x := by aesop
  probOutput_selectElem_eq x y := by grind
