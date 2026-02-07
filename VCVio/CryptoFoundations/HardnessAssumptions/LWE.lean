/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.Constructions.UniformSelect

/-!
# Learning With Errors

This file gives a general definition of the LWE problem. It is parameterized by the following:
- `n`: the dimension of the secret
- `m`: the number of samples
- `p`: the modulus (not necessarily prime)
- `errSamp : ProbComp (Fin p)`: a probabilistic sampling algorithm for the error

(`errSamp` can potentially be replaced with `χ : PMF (Fin p)` instead, to be used with
`evalDistWhen` with non-uniform distributions)

We define the (decision) LWE problem as a security experiment on an oracle that takes as input:
- A matrix `A : Fin m → Fin n → Fin p`
- A vector `u : Fin m → Fin p`, either sampled uniformly at random, or sampled from the LWE
  distribution `s * A + e`, where `s : Fin n → Fin p` is the secret and `e : Fin m → Fin p` has
  every entry sampled from `errSamp`.

The adversary wins if it can correctly guess which case the distribution is.

The search LWE problem instead asks that the adversary given `A` and `u = s * A + e` outputs the
secret `s`.
-/

open OracleComp OracleSpec ENNReal

variable (n m p : ℕ) [NeZero p] (errSamp : ProbComp (Fin p))

/-- The LWE distribution `(A, s * A + e)` -/
def LWE_Distr : ProbComp (Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let s ←$ᵗ Vector (Fin p) n
  -- Sampled each entry of `e` independently using `errSamp`
  let e ← (Vector.range m).mapM (fun _ ↦ errSamp)
  let u := A.vecMul s.get + e.get
  return (A, Vector.ofFn u)

/-- The uniform distribution `(A, u)` -/
def LWE_Uniform_Distr : ProbComp (Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  return (A, u)

/-- An adversary for the decisional LWE problem. Takes in a pair `(A, u)` and outputs a boolean. -/
def LWE_Adversary := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp Bool

/-- The decisional LWE experiment. If `b = true`, the distribution is LWE,
otherwise it is uniform. -/
def LWE_Experiment (adv : LWE_Adversary n m p) : ProbComp Bool := do
  let b ←$ᵗ Bool
  let distr ← if b then LWE_Distr n m p errSamp else LWE_Uniform_Distr n m p
  let b' ← adv distr
  return b' = b

noncomputable def LWE_Advantage (adv : LWE_Adversary n m p) : ℝ :=
  (LWE_Experiment n m p errSamp adv).advantage'

-- Alternate definition of the decisional LWE assumption, based on two games instead of one

/-- The first game of the decisional LWE assumption, where the distribution is LWE.

(we map `true` to `()` and `false` to `failure`) -/
def LWE_Game_0 (adv : LWE_Adversary n m p) : ProbComp Bool := do
  let distr ← LWE_Distr n m p errSamp
  let b ← adv distr
  return b

/-- The second game of the decisional LWE assumption, where the distribution is uniform.

(we map `true` to `()` and `false` to `failure`) -/
def LWE_Game_1 (adv : LWE_Adversary n m p) : ProbComp Bool := do
  let distr ← LWE_Uniform_Distr n m p
  let b ← adv distr
  return b

/-- An adversary for the search LWE problem. Takes in a pair `(A, u)` and outputs a vector `s`. -/
def LWE_Search_Adversary :=
  Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp (Vector (Fin p) n)

/-- The search LWE experiment. The adversary wins if it can correctly guess the secret `s`. -/
def LWE_Search_Experiment (adv : LWE_Search_Adversary n m p) : ProbComp Bool := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let s ←$ᵗ Vector (Fin p) n
  -- Sampled each entry of `e` independently using `errSamp`
  let e ← (Vector.range m).mapM (fun _ ↦ errSamp)
  let u := A.vecMul s.get + e.get
  let s' ← adv (A, Vector.ofFn u)
  return s' = s

noncomputable def LWE_Search_Advantage (adv : LWE_Search_Adversary n m p) : ℝ :=
  (LWE_Search_Experiment n m p errSamp adv).advantage'

/-- The two ways of defining the decisional LWE assumption (via a single experiment or via two
  games) are equivalent.

(probably not correct) -/
lemma LWE_Experiment_eq_LWE_Game_01 {n m p : ℕ} [NeZero p] {errSamp : ProbComp (Fin p)}
    {adv : LWE_Adversary n m p} :
    2 * (LWE_Experiment n m p errSamp adv).advantage' =
      (LWE_Game_0 n m p errSamp adv).advantage₂' (LWE_Game_1 n m p adv) := by
  unfold LWE_Experiment LWE_Game_0 LWE_Game_1 ProbComp.advantage' ProbComp.advantage₂'
  rw [probOutput_bind_eq_sum_finSupport, probOutput_bind_eq_sum_finSupport]
  simp
  -- so painful...
  rw [mul_abs_of_nonneg (by simp), mul_sub]
  rw [← toReal_ofReal_mul _ _ (by simp), ← toReal_ofReal_mul _ _ (by simp)]
  rw [ofReal_ofNat, mul_add, mul_add]
  rw [← mul_assoc 2 _ _, ← mul_assoc 2 _ _, ← mul_assoc 2 _ _, ← mul_assoc 2 _ _]
  rw [ENNReal.mul_inv_cancel (by simp) (by simp)]
  simp
  rw [toReal_add (by simp) (by simp), toReal_add (by simp) (by simp)]
  rw [probOutput_false_eq_probOutput_true_not, probOutput_false_eq_probOutput_true_not]
  simp
  -- probably not correct...
  sorry
