/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.TVDist
import VCVio.EvalDist.Defs.Semantics

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
/-- Triangle inequality for Boolean distinguishing advantage. -/
lemma ProbComp.boolDistAdvantage_triangle (p q r : ProbComp Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r := by
  unfold ProbComp.boolDistAdvantage
  exact abs_sub_le _ _ _
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
      let b ← ($ᵗ Bool : ProbComp Bool)
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
      let b ← ($ᵗ Bool : ProbComp Bool)
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
    let b ← ($ᵗ Bool : ProbComp Bool)
    let z ← if b then real a else rand a
    pure (b == z)
  let left : ProbComp Bool := do
    let a ← pref
    real a
  let right : ProbComp Bool := do
    let a ← pref
    rand a
  let branchGame : ProbComp Bool := do
    let b ← ($ᵗ Bool : ProbComp Bool)
    let z ← if b then left else right
    pure (b == z)
  have hbranch : evalDist game = evalDist branchGame := by
    apply evalDist_ext
    intro x
    calc
      Pr[= x | game] =
          Pr[= x | do
            let b ← ($ᵗ Bool : ProbComp Bool)
            let a ← pref
            let z ← if b then real a else rand a
            pure (b == z)] := by
              simpa [game, bind_assoc] using
                (probOutput_bind_bind_swap pref ($ᵗ Bool : ProbComp Bool)
                  (fun a b => do
                    let z ← if b then real a else rand a
                    pure (b == z))
                  x)
      _ = Pr[= x | branchGame] := by
            refine probOutput_bind_congr' ($ᵗ Bool : ProbComp Bool) x ?_
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
