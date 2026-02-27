/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Monad.Map

/-!
# Evaluation Distributions of Computations with `BitVec`

Lemmas about `probOutput` involving `BitVec`, generic over any monad `m` with `[HasEvalSPMF m]`.

The `SampleableType (BitVec n)` instance is defined in
`VCVio.OracleComp.Constructions.SampleableType`.
-/

open BitVec

variable {α β γ : Type _}
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]

@[simp, grind =]
lemma probOutput_ofFin_map {n : ℕ} (mx : m (Fin (2 ^ n))) (x : BitVec n) :
    Pr[= x | ofFin <$> mx] = Pr[= toFin x | mx] := by aesop

@[simp, grind =]
lemma probOutput_bitVec_toFin_map {n : ℕ} (mx : m (BitVec n)) (x : Fin (2 ^ n)) :
    Pr[= x | toFin <$> mx] = Pr[= ofFin x | mx] := by aesop

lemma probOutput_xor_map {n : ℕ} (mx : m (BitVec n)) (x y : BitVec n) :
    Pr[= y | (x ^^^ ·) <$> mx] = Pr[= x ^^^ y | mx] := by
  have hinj : Function.Injective (x ^^^ ·) := fun a b h => by
    have := congrArg (x ^^^ ·) h; simp at this; exact this
  conv_lhs => rw [show y = x ^^^ (x ^^^ y) by simp]
  exact probOutput_map_injective mx hinj (x ^^^ y)
