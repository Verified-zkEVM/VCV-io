/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.TVDist
import VCVio.EvalDist.Defs.Semantics
import VCVio.EvalDist.Defs.Instances
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Security Experiments

This file defines simple security experiments that succeed unless they terminate with failure.
Each experiment carries bundled subprobabilistic semantics, so the experiment can be interpreted
through an internal semantic monad instead of requiring a global `HasEvalSPMF` instance on the
ambient monad.

We also define `BoundedAdversary α β` as an oracle computation bundled with a query bound.
-/

universe u v w

open OracleComp OracleSpec ENNReal Polynomial Prod

/-- Bias advantage of a Boolean-valued game: the gap between the probabilities of the two outputs.

This is the canonical single-game formulation for hidden-bit guessing experiments. -/
noncomputable def ProbComp.boolBiasAdvantage (p : ProbComp Bool) : ℝ :=
  |(Pr[= true | p]).toReal - (Pr[= false | p]).toReal|

/-- Distinguishing advantage between two Boolean-valued games, measured on the `true` branch.

For Boolean outputs this is equivalent to measuring the gap on `false`; choosing `true` is just a
conventional presentation. -/
noncomputable def ProbComp.boolDistAdvantage (p q : ProbComp Bool) : ℝ :=
  |(Pr[= true | p]).toReal - (Pr[= true | q]).toReal|

/-- Bias advantage of a Boolean-valued subdistribution: the gap between the probabilities of
returning `true` and `false`.

This is the `SPMF` analogue of `ProbComp.boolBiasAdvantage`, used for games that have already
been observed under bundled subprobabilistic semantics. Any remaining mass corresponds to failure
and therefore contributes to neither Boolean branch. -/
noncomputable def SPMF.boolBiasAdvantage (p : SPMF Bool) : ℝ :=
  |(Pr[= true | p]).toReal - (Pr[= false | p]).toReal|

/-- Distinguishing advantage between two Boolean-valued subdistributions, measured on the `true`
branch.

This is the `SPMF` analogue of `ProbComp.boolDistAdvantage`. -/
noncomputable def SPMF.boolDistAdvantage (p q : SPMF Bool) : ℝ :=
  |(Pr[= true | p]).toReal - (Pr[= true | q]).toReal|

@[simp]
lemma SPMF.boolDistAdvantage_self (p : SPMF Bool) : p.boolDistAdvantage p = 0 := by
  simp [SPMF.boolDistAdvantage]

lemma SPMF.boolDistAdvantage_comm (p q : SPMF Bool) :
    p.boolDistAdvantage q = q.boolDistAdvantage p := by
  unfold SPMF.boolDistAdvantage
  exact abs_sub_comm _ _

lemma SPMF.boolDistAdvantage_nonneg (p q : SPMF Bool) : 0 ≤ p.boolDistAdvantage q :=
  abs_nonneg _

/-- Triangle inequality for SPMF Boolean distinguishing advantage. -/
lemma SPMF.boolDistAdvantage_triangle (p q r : SPMF Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r := by
  unfold SPMF.boolDistAdvantage
  exact abs_sub_le _ _ _

/-- Telescoping triangle inequality across a finite chain of SPMF games. -/
lemma SPMF.boolDistAdvantage_le_sum_range {n : ℕ} (games : ℕ → SPMF Bool) :
    (games 0).boolDistAdvantage (games n) ≤
      ∑ i ∈ Finset.range n, (games i).boolDistAdvantage (games (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (games 0).boolDistAdvantage (games (n + 1))
      _ ≤ (games 0).boolDistAdvantage (games n) +
          (games n).boolDistAdvantage (games (n + 1)) :=
          SPMF.boolDistAdvantage_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.range n, (games i).boolDistAdvantage (games (i + 1))) +
          (games n).boolDistAdvantage (games (n + 1)) := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (games i).boolDistAdvantage (games (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- Bound the `true`-branch probability of one SPMF game in terms of another plus their
distinguishing advantage. SPMF analogue of
`ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage`. -/
lemma SPMF.probOutput_true_le_add_ofReal_boolDistAdvantage (p q : SPMF Bool) :
    Pr[= true | p] ≤ Pr[= true | q] + ENNReal.ofReal (p.boolDistAdvantage q) := by
  unfold SPMF.boolDistAdvantage
  set a : ℝ := (Pr[= true | p]).toReal with ha_def
  set b : ℝ := (Pr[= true | q]).toReal with hb_def
  have h_abs : a ≤ b + |a - b| := by
    have : a - b ≤ |a - b| := le_abs_self _
    linarith
  have h_p : Pr[= true | p] = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal probOutput_ne_top).symm
  have h_q : Pr[= true | q] = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal probOutput_ne_top).symm
  rw [h_p, h_q, ← ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h_abs

/-- Signed Boolean advantage of an SPMF game: `Pr[true] - Pr[false]` (as a real number).

`SPMF.boolBiasAdvantage` is the absolute value of this. Working at the signed level avoids the
failure-mass bookkeeping otherwise needed to relate biases of branch games to biases of the
underlying real/random branches: the algebraic identity
`signedBoolAdv (uniformBool branch) = (signedBoolAdv real - signedBoolAdv rand) / 2`
holds for any pair of branches regardless of their failure probabilities. -/
noncomputable def SPMF.signedBoolAdv (p : SPMF Bool) : ℝ :=
  (Pr[= true | p]).toReal - (Pr[= false | p]).toReal

@[simp]
lemma SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv (p : SPMF Bool) :
    p.boolBiasAdvantage = |p.signedBoolAdv| := rfl

/-- Triangle inequality on Boolean bias, viewed through the signed advantage: the bias of any
SPMF is bounded by the absolute difference of its signed advantage from any reference, plus the
bias of that reference. -/
lemma SPMF.boolBiasAdvantage_le_abs_sub_add_boolBiasAdvantage
    (p q : SPMF Bool) :
    p.boolBiasAdvantage ≤ |p.signedBoolAdv - q.signedBoolAdv| + q.boolBiasAdvantage := by
  rw [SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv,
      SPMF.boolBiasAdvantage_eq_abs_signedBoolAdv]
  have := abs_sub_le p.signedBoolAdv q.signedBoolAdv 0
  simpa using this

/-- Conditioning on a fair non-failing Boolean SPMF averages the two branch probabilities.
The ProbComp analogue is `probOutput_bind_uniformBool` in
`OracleComp/Constructions/SampleableType.lean`; this is the SPMF version, used to expand a
hidden-bit branch game's distribution under bundled subprobabilistic semantics. -/
lemma SPMF.probOutput_bind_uniformBool_of_half {α : Type}
    (b : SPMF Bool) (hfail : Pr[⊥ | b] = 0) (huniform : Pr[= true | b] = 1 / 2)
    (f : Bool → SPMF α) (x : α) :
    Pr[= x | (do let t ← b; f t)] =
      (Pr[= x | f true] + Pr[= x | f false]) / 2 := by
  have hfalse : Pr[= false | b] = 1 / 2 := by
    have hsum : ∑ y : Bool, Pr[= y | b] = 1 - Pr[⊥ | b] := sum_probOutput_eq_sub b
    rw [Fintype.sum_bool, huniform, hfail, tsub_zero, add_comm] at hsum
    have h12 : (1 / 2 : ℝ≥0∞) ≠ ∞ := by
      rw [show (1 / 2 : ℝ≥0∞) = 2⁻¹ from one_div 2]
      exact ENNReal.inv_ne_top.mpr (by norm_num)
    have h := ENNReal.eq_sub_of_add_eq h12 hsum
    rw [h, show (1 : ℝ≥0∞) / 2 = 2⁻¹ from one_div 2, ENNReal.one_sub_inv_two, ← one_div]
  rw [probOutput_bind_eq_tsum, tsum_fintype (L := .unconditional _), Fintype.sum_bool,
    huniform, hfalse, one_div, ← mul_add, mul_comm, ← div_eq_mul_inv]

/-! ### Branch-game congruence and closed forms

Helpers shared by the four hidden-bit branch-game lemmas below: a pointwise
`Pr[= x | ·]` congruence for `signedBoolAdv` / `boolBiasAdvantage`, the closed
form for `Pr[= x | branchGame]` averaging the two branches, and an `evalDist`
swap lemma that pulls a prefix sample past the hidden bit. -/

/-- Two SPMFs with equal pointwise `Pr[= x | ·]` outputs have equal signed advantage. -/
lemma SPMF.signedBoolAdv_congr {p q : SPMF Bool}
    (h : ∀ x : Bool, Pr[= x | p] = Pr[= x | q]) :
    p.signedBoolAdv = q.signedBoolAdv := by
  unfold SPMF.signedBoolAdv; rw [h true, h false]

/-- Two SPMFs with equal pointwise `Pr[= x | ·]` outputs have equal bias advantage. -/
lemma SPMF.boolBiasAdvantage_congr {p q : SPMF Bool}
    (h : ∀ x : Bool, Pr[= x | p] = Pr[= x | q]) :
    p.boolBiasAdvantage = q.boolBiasAdvantage := by
  unfold SPMF.boolBiasAdvantage; rw [h true, h false]

/-- Closed form for the output probabilities of a hidden-bit branch game over two SPMF branches:
`Pr[= x | branchGame] = (Pr[= x | real] + Pr[= !x | rand]) / 2`. -/
private lemma SPMF.probOutput_branchGame_uniformBool
    (real rand : SPMF Bool) (b : SPMF Bool)
    (hfail_b : Pr[⊥ | b] = 0) (huniform_b : Pr[= true | b] = 1 / 2) (x : Bool) :
    Pr[= x | (do
      let t ← b
      let z ← if t then real else rand
      pure (t == z) : SPMF Bool)] =
        (Pr[= x | real] + Pr[= !x | rand]) / 2 := by
  have h_id : (BEq.beq true : Bool → Bool) = id := by funext z; cases z <;> rfl
  have h_not : (BEq.beq false : Bool → Bool) = (! ·) := by funext z; cases z <;> rfl
  have hgame_eq :
      (do
        let t ← b
        let z ← if t then real else rand
        pure (t == z) : SPMF Bool) =
        (b >>= fun t => if t then ((true == ·) <$> real) else ((false == ·) <$> rand)) := by
    apply bind_congr; intro t
    cases t <;> simp [bind_pure_comp]
  rw [hgame_eq, SPMF.probOutput_bind_uniformBool_of_half b hfail_b huniform_b _ x,
    h_id, h_not, id_map]
  cases x
  · simp [probOutput_not_map']
  · simp [probOutput_not_map]

/-- Pulling a prefix sample past the hidden bit preserves the `evalDist` of a branch game:
`𝒟[bind pref ; branch] = 𝒟[branch with prefixes bound inside]`. -/
private lemma SPMF.evalDist_branchGame_bind_swap {α : Type}
    (pref : SPMF α) (real rand : α → SPMF Bool) (b : SPMF Bool) :
    𝒟[(do
        let a ← pref
        let t ← b
        let z ← if t then real a else rand a
        pure (t == z) : SPMF Bool)] =
    𝒟[(do
        let t ← b
        let z ← if t then (pref >>= real) else (pref >>= rand)
        pure (t == z) : SPMF Bool)] := by
  apply evalDist_ext
  intro x
  calc
    Pr[= x | (do
        let a ← pref
        let t ← b
        let z ← if t then real a else rand a
        pure (t == z) : SPMF Bool)] =
        Pr[= x | (do
          let t ← b
          let a ← pref
          let z ← if t then real a else rand a
          pure (t == z) : SPMF Bool)] := by
      simpa [bind_assoc] using
        (probOutput_bind_bind_swap pref b
          (fun a t => do
            let z ← if t then real a else rand a
            pure (t == z))
          x)
    _ = Pr[= x | (do
        let t ← b
        let z ← if t then (pref >>= real) else (pref >>= rand)
        pure (t == z) : SPMF Bool)] := by
      refine probOutput_bind_congr' b x ?_
      intro t
      cases t <;> simp

/-! ### Branch-game advantage equalities -/

/-- A hidden-bit guessing game over two SPMF branches has Boolean bias equal to the distinguishing
advantage between those branches, provided the two branches share the same failure mass.

The matching-failure hypothesis is genuinely needed at the SPMF level: signed Boolean advantage
of the branch game is `(signedBoolAdv real - signedBoolAdv rand) / 2` regardless, but converting
that signed difference into a `Pr[= true]`-only difference (which is what `boolDistAdvantage`
measures) requires the failure terms to cancel. -/
lemma SPMF.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch_of_failure_eq
    (real rand : SPMF Bool) (b : SPMF Bool)
    (hfail_b : Pr[⊥ | b] = 0) (huniform_b : Pr[= true | b] = 1 / 2)
    (hfail_eq : Pr[⊥ | real] = Pr[⊥ | rand]) :
    (do
      let t ← b
      let z ← if t then real else rand
      pure (t == z)).boolBiasAdvantage =
    real.boolDistAdvantage rand := by
  have hT := SPMF.probOutput_branchGame_uniformBool real rand b hfail_b huniform_b true
  have hF := SPMF.probOutput_branchGame_uniformBool real rand b hfail_b huniform_b false
  simp only [Bool.not_true, Bool.not_false] at hT hF
  unfold SPMF.boolBiasAdvantage SPMF.boolDistAdvantage
  rw [hT, hF]
  set pT_r : ℝ := (Pr[= true | real]).toReal
  set pF_r : ℝ := (Pr[= false | real]).toReal
  set pT_q : ℝ := (Pr[= true | rand]).toReal
  set pF_q : ℝ := (Pr[= false | rand]).toReal
  have hsum_r : pT_r + pF_r = 1 - (Pr[⊥ | real]).toReal := by
    rw [show pT_r + pF_r = (Pr[= true | real] + Pr[= false | real]).toReal from
      (ENNReal.toReal_add probOutput_ne_top probOutput_ne_top).symm,
      probOutput_true_add_false,
      ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top, ENNReal.toReal_one]
  have hsum_q : pT_q + pF_q = 1 - (Pr[⊥ | rand]).toReal := by
    rw [show pT_q + pF_q = (Pr[= true | rand] + Pr[= false | rand]).toReal from
      (ENNReal.toReal_add probOutput_ne_top probOutput_ne_top).symm,
      probOutput_true_add_false,
      ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top, ENNReal.toReal_one]
  have hbot_eq : (Pr[⊥ | real]).toReal = (Pr[⊥ | rand]).toReal := by rw [hfail_eq]
  have htoR1 : ((Pr[= true | real] + Pr[= false | rand]) / 2).toReal = (pT_r + pF_q) / 2 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_add probOutput_ne_top probOutput_ne_top]
    rfl
  have htoR2 : ((Pr[= false | real] + Pr[= true | rand]) / 2).toReal = (pF_r + pT_q) / 2 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_add probOutput_ne_top probOutput_ne_top]
    rfl
  rw [htoR1, htoR2]
  have hkey : (pT_r + pF_q) / 2 - (pF_r + pT_q) / 2 = pT_r - pT_q := by
    have h_pf_r : pF_r = 1 - (Pr[⊥ | real]).toReal - pT_r := by linarith
    have h_pf_q : pF_q = 1 - (Pr[⊥ | rand]).toReal - pT_q := by linarith
    rw [h_pf_r, h_pf_q, ← hbot_eq]; ring
  rw [hkey]

/-- Algebraic identity for signed Boolean advantage of a uniform-Bool branch game: the signed
advantage of a hidden-bit guessing game between two SPMF branches equals half the difference of
the branches' signed advantages. Unlike the `boolDistAdvantage` form, this holds with no
failure-mass hypothesis on the branches — the failure terms cancel symmetrically when computing
the signed advantage of the branch game. -/
lemma SPMF.signedBoolAdv_uniformBool_branch
    (real rand : SPMF Bool) (b : SPMF Bool)
    (hfail_b : Pr[⊥ | b] = 0) (huniform_b : Pr[= true | b] = 1 / 2) :
    (do
      let t ← b
      let z ← if t then real else rand
      pure (t == z)).signedBoolAdv =
    (real.signedBoolAdv - rand.signedBoolAdv) / 2 := by
  have hT := SPMF.probOutput_branchGame_uniformBool real rand b hfail_b huniform_b true
  have hF := SPMF.probOutput_branchGame_uniformBool real rand b hfail_b huniform_b false
  simp only [Bool.not_true, Bool.not_false] at hT hF
  unfold SPMF.signedBoolAdv
  rw [hT, hF, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top]
  simp only [ENNReal.toReal_ofNat]
  ring

/-- Shared-prefix variant of `signedBoolAdv_uniformBool_branch`: a `pref` is sampled before the
hidden-bit decision, and `real` / `rand` are families indexed by the prefix output. No
failure-mass hypothesis is needed. -/
lemma SPMF.signedBoolAdv_bind_uniformBool
    {α : Type} (pref : SPMF α) (real rand : α → SPMF Bool) (b : SPMF Bool)
    (hfail_b : Pr[⊥ | b] = 0) (huniform_b : Pr[= true | b] = 1 / 2) :
    (do
      let a ← pref
      let t ← b
      let z ← if t then real a else rand a
      pure (t == z)).signedBoolAdv =
    ((do let a ← pref; real a).signedBoolAdv -
      (do let a ← pref; rand a).signedBoolAdv) / 2 := by
  rw [SPMF.signedBoolAdv_congr (evalDist_ext_iff.mp
    (SPMF.evalDist_branchGame_bind_swap pref real rand b))]
  exact SPMF.signedBoolAdv_uniformBool_branch _ _ b hfail_b huniform_b

/-- Shared-prefix variant of
`boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch_of_failure_eq`: the prefix `pref` is
sampled before the hidden-bit decision, and `real` / `rand` are families indexed by `pref`'s
output. The failure-equality hypothesis is pointwise over `support pref`. -/
lemma SPMF.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage_of_failure_eq
    {α : Type} (pref : SPMF α) (real rand : α → SPMF Bool) (b : SPMF Bool)
    (hfail_b : Pr[⊥ | b] = 0) (huniform_b : Pr[= true | b] = 1 / 2)
    (hfail_eq : ∀ a ∈ support pref, Pr[⊥ | real a] = Pr[⊥ | rand a]) :
    (do
      let a ← pref
      let t ← b
      let z ← if t then real a else rand a
      pure (t == z)).boolBiasAdvantage =
    (do
      let a ← pref
      real a).boolDistAdvantage
      (do
        let a ← pref
        rand a) := by
  have hfail_left_right :
      Pr[⊥ | (do let a ← pref; real a : SPMF Bool)] =
        Pr[⊥ | (do let a ← pref; rand a : SPMF Bool)] := by
    change Pr[⊥ | pref >>= real] = Pr[⊥ | pref >>= rand]
    rw [probFailure_bind_eq_add_tsum_support, probFailure_bind_eq_add_tsum_support]
    congr 1
    refine tsum_congr fun a => ?_
    rw [hfail_eq a a.2]
  rw [SPMF.boolBiasAdvantage_congr (evalDist_ext_iff.mp
    (SPMF.evalDist_branchGame_bind_swap pref real rand b))]
  exact SPMF.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch_of_failure_eq
    _ _ b hfail_b huniform_b hfail_left_right

/-- Triangle inequality for Boolean distinguishing advantage. -/
lemma ProbComp.boolDistAdvantage_triangle (p q r : ProbComp Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r := by
  unfold ProbComp.boolDistAdvantage
  exact abs_sub_le _ _ _

/-- The `true`-branch probability of one Boolean-valued game is bounded above by the
`true`-branch probability of another game plus their distinguishing advantage.

This is the `ENNReal`-level interpretation of the real-valued identity `a ≤ b + |a - b|`,
packaged for SSP game-hopping: converting an `advantage p q ≤ ε` assumption into a direct
probability inequality `Pr[true|p] ≤ Pr[true|q] + ENNReal.ofReal ε` that plugs into chained
`calc`-style bounds. -/
lemma ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    Pr[= true | p] ≤ Pr[= true | q] + ENNReal.ofReal (p.boolDistAdvantage q) := by
  unfold ProbComp.boolDistAdvantage
  set a : ℝ := (Pr[= true | p]).toReal with ha_def
  set b : ℝ := (Pr[= true | q]).toReal with hb_def
  have h_abs : a ≤ b + |a - b| := by
    have : a - b ≤ |a - b| := le_abs_self _
    linarith
  have h_p : Pr[= true | p] = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal probOutput_ne_top).symm
  have h_q : Pr[= true | q] = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal probOutput_ne_top).symm
  rw [h_p, h_q, ← ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h_abs
/-- Re-express Boolean bias as twice the absolute deviation of `Pr[true]` from `1/2`. -/
lemma ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half (p : ProbComp Bool) :
    p.boolBiasAdvantage = 2 * |(Pr[= true | p]).toReal - 1 / 2| := by
  have hfalse : Pr[= false | p] = 1 - Pr[= true | p] := by
    have hsum : Pr[= true | p] + Pr[= false | p] = 1 := by simp
    rw [← hsum, ENNReal.add_sub_cancel_left probOutput_ne_top]
  unfold ProbComp.boolBiasAdvantage
  rw [hfalse, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  rw [ENNReal.toReal_one]
  rw [show (Pr[= true | p]).toReal - (1 - (Pr[= true | p]).toReal) =
      2 * ((Pr[= true | p]).toReal - 1 / 2) by ring]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]

/-- A hidden-bit guessing game over two Boolean branches has bias exactly equal to the
distinguishing advantage between those two branches. -/
lemma ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch
    (real rand : ProbComp Bool) :
    (do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)).boolBiasAdvantage =
    real.boolDistAdvantage rand := by
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half]
  rw [probOutput_uniformBool_branch_toReal_sub_half]
  unfold ProbComp.boolDistAdvantage
  calc
    2 * |((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2|
        = |(2 : ℝ)| * |((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2| := by
            norm_num
    _ = |(2 : ℝ) * (((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2)| := by
          rw [← abs_mul]
    _ = |(Pr[= true | real]).toReal - (Pr[= true | rand]).toReal| := by
          congr 1
          ring

/-- Version of `boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch` with a shared sampled
prefix before the real/random branch is chosen. -/
lemma ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
    {α : Type} (pref : ProbComp α) (real rand : α → ProbComp Bool) :
    (do
      let a ← pref
      let b ← ($ᵗ Bool)
      let z ← if b then real a else rand a
      pure (b == z)).boolBiasAdvantage =
    (do
      let a ← pref
      real a).boolDistAdvantage
      (do
        let a ← pref
        rand a) := by
  let game : ProbComp Bool := do
    let a ← pref
    let b ← ($ᵗ Bool)
    let z ← if b then real a else rand a
    pure (b == z)
  let left : ProbComp Bool := do
    let a ← pref
    real a
  let right : ProbComp Bool := do
    let a ← pref
    rand a
  let branchGame : ProbComp Bool := do
    let b ← ($ᵗ Bool)
    let z ← if b then left else right
    pure (b == z)
  have hbranch : 𝒟[game] = 𝒟[branchGame] := by
    apply evalDist_ext
    intro x
    calc
      Pr[= x | game] =
          Pr[= x | do
            let b ← ($ᵗ Bool)
            let a ← pref
            let z ← if b then real a else rand a
            pure (b == z)] := by
              simpa [game, bind_assoc] using
                (probOutput_bind_bind_swap pref ($ᵗ Bool)
                  (fun a b => do
                    let z ← if b then real a else rand a
                    pure (b == z))
                  x)
      _ = Pr[= x | branchGame] := by
            refine probOutput_bind_congr' ($ᵗ Bool) x ?_
            intro b
            cases b <;> simp [left, right]
  have hprob := evalDist_ext_iff.mp hbranch
  rw [show game.boolBiasAdvantage = branchGame.boolBiasAdvantage by
    unfold ProbComp.boolBiasAdvantage
    rw [hprob true, hprob false]]
  simpa [branchGame, left, right] using
    ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch left right

/-- The **advantage** of a game `p`, assumed to be a probabilistic computation ending with a `guard`
  statement, is the absolute difference between the probability of success and 1/2. -/
noncomputable def ProbComp.guessAdvantage (p : ProbComp Unit) : ℝ := |1 / 2 - (Pr[= () | p]).toReal|

lemma ProbComp.guessAdvantage_eq_half_sub_probFailure (p : ProbComp Unit) :
    p.guessAdvantage = |1 / 2 - (Pr[⊥ | p]).toReal| := by
  have h : Pr[= () | p] = 1 - Pr[⊥ | p] := probOutput_eq_sub_probFailure_of_unit
  simp only [guessAdvantage, h,
    ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top, ENNReal.toReal_one]
  rw [show (1 : ℝ) / 2 - (1 - (Pr[⊥ | p]).toReal) = (Pr[⊥ | p]).toReal - 1 / 2 from by ring]
  exact abs_sub_comm _ _

lemma ProbComp.guessAdvantage_eq_half_of_sub (p : ProbComp Unit) :
    p.guessAdvantage = 2⁻¹ * |(Pr[⊥ | p]).toReal - (Pr[= () | p]).toReal| := by
  have h : Pr[= () | p] = 1 - Pr[⊥ | p] := probOutput_eq_sub_probFailure_of_unit
  simp only [guessAdvantage, h,
    ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top, ENNReal.toReal_one]
  set f := (Pr[⊥ | p]).toReal with hf_def
  have h1 : f - (1 - f) = 2 * f - 1 := by ring
  have h2 : (1 : ℝ) / 2 - (1 - f) = f - 1 / 2 := by ring
  rw [h1, h2]
  have h3 : 2 * f - 1 = 2 * (f - 1 / 2) := by ring
  rw [h3, abs_mul, abs_of_pos (by positivity : (2 : ℝ) > 0)]
  ring

/-- The **advantage** between two games `p` and `q`, modeled as probabilistic computations returning
  `Unit`, is the absolute difference between their probabilities of success. -/
noncomputable def ProbComp.distAdvantage (p q : ProbComp Unit) : ℝ :=
  |(Pr[= () | p]).toReal - (Pr[= () | q]).toReal|

@[simp]
lemma ProbComp.distAdvantage_self (p : ProbComp Unit) : p.distAdvantage p = 0 := by
  simp [ProbComp.distAdvantage]

lemma ProbComp.distAdvantage_comm (p q : ProbComp Unit) :
    p.distAdvantage q = q.distAdvantage p := by
  unfold ProbComp.distAdvantage
  exact abs_sub_comm _ _

lemma ProbComp.distAdvantage_eq_abs_sub_probFailure (p q : ProbComp Unit) :
    p.distAdvantage q = |(Pr[⊥ | p]).toReal - (Pr[⊥ | q]).toReal| := by
  have hp : Pr[= () | p] = 1 - Pr[⊥ | p] := probOutput_eq_sub_probFailure_of_unit
  have hq : Pr[= () | q] = 1 - Pr[⊥ | q] := probOutput_eq_sub_probFailure_of_unit
  simp only [distAdvantage, hp, hq,
    ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top, ENNReal.toReal_one]
  rw [show (1 - (Pr[⊥ | p]).toReal) - (1 - (Pr[⊥ | q]).toReal) =
    -((Pr[⊥ | p]).toReal - (Pr[⊥ | q]).toReal) from by ring]
  exact abs_neg _

lemma ProbComp.distAdvantage_nonneg (p q : ProbComp Unit) : 0 ≤ p.distAdvantage q :=
  abs_nonneg _

lemma ProbComp.distAdvantage_triangle (p q r : ProbComp Unit) :
    p.distAdvantage r ≤ p.distAdvantage q + q.distAdvantage r := by
  unfold distAdvantage; exact abs_sub_le _ _ _

lemma ProbComp.distAdvantage_le_sum_range {n : ℕ} (games : ℕ → ProbComp Unit) :
    (games 0).distAdvantage (games n) ≤
      ∑ i ∈ Finset.range n, (games i).distAdvantage (games (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (games 0).distAdvantage (games (n + 1))
      _ ≤ (games 0).distAdvantage (games n) + (games n).distAdvantage (games (n + 1)) :=
          distAdvantage_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.range n, (games i).distAdvantage (games (i + 1))) +
          (games n).distAdvantage (games (n + 1)) := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (games i).distAdvantage (games (i + 1)) := by
          rw [Finset.sum_range_succ]

lemma ProbComp.distAdvantage_eq_tvDist (p q : ProbComp Unit) :
    p.distAdvantage q = tvDist p q := by
  simp only [distAdvantage, tvDist, SPMF.tvDist, PMF.tvDist_option_punit]
  rfl

/-- A security adversary bundling a computation with a bound on the number of queries it makes,
where the bound must be shown to satisfy `IsQueryBound`.
We also require an explicit list of all oracles used in the computation,
which is necessary in order to make certain reductions computable. -/
structure BoundedAdversary {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0

namespace BoundedAdversary

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

end BoundedAdversary

/-- Structure to represent a security experiment.
The experiment is considered successful unless it terminates with failure.

A `SecExp` carries bundled `SPMFSemantics` directly. This keeps the semantic assumptions attached
to the experiment itself: the surface monad can be interpreted through some internal semantic
monad, and only then observed as a subdistribution for measuring success and failure
probabilities. -/
structure SecExp (m : Type → Type w) [Monad m]
    extends SPMFSemantics m where
  /-- Main experiment body. Success is interpreted as terminating without failure. -/
  main : m Unit

namespace SecExp

variable {m : Type → Type w} [Monad m]

section advantage

/-- Advantage of a failure-based security experiment: one minus its failure probability. -/
noncomputable def advantage (exp : SecExp m) : ℝ≥0∞ :=
  1 - Pr[⊥ | exp.toSPMFSemantics.evalDist exp.main]

/-- A failure-based experiment has zero advantage exactly when it fails with probability `1`. -/
@[simp]
lemma advantage_eq_zero_iff (exp : SecExp m) :
    exp.advantage = 0 ↔ Pr[⊥ | exp.toSPMFSemantics.evalDist exp.main] = 1 := by
  rw [advantage, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm (exp.toSPMFSemantics.probFailure_le_one _) h,
    fun h => h ▸ le_refl _⟩

/-- A failure-based experiment has advantage `1` exactly when it never fails. -/
@[simp]
lemma advantage_eq_one_iff (exp : SecExp m) :
    exp.advantage = 1 ↔ Pr[⊥ | exp.toSPMFSemantics.evalDist exp.main] = 0 := by
  constructor
  · intro h; by_contra hne
    have : exp.advantage < 1 := by
      unfold advantage; exact ENNReal.sub_lt_self one_ne_top one_ne_zero hne
    exact absurd h (ne_of_lt this)
  · intro h; simp [advantage, h]

end advantage

end SecExp
