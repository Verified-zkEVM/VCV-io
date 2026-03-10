/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.ExecutionMethod
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.TVDist

/-!
# Security Experiments

This file gives a basic way to represent security experiments, as an extension of `OracleAlg`.
The definition is meant to be simple enough to give useful lemmas while still being
able to represent most common use cases.

We also give a definition `BoundedAdversary α β` of a security adversary with input `α` and output `β`,
as just a computation bundled with a bound on the number of queries it makes.

The main definition is `SecExp spec α β`, which extends `OracleAlg` with three functions:
* `inp_gen` that chooses an input for the experiment of type `α`
* `main` that takes an input and computes a result of type `β`
* `isValid` that decides whether the experiment succeeded
-/

universe u v w

open OracleComp OracleSpec ENNReal Polynomial Prod

noncomputable def ProbComp.boolBiasAdvantage (p : ProbComp Bool) : ℝ :=
  |(Pr[= true | p]).toReal - (Pr[= false | p]).toReal|

noncomputable def ProbComp.boolDistAdvantage (p q : ProbComp Bool) : ℝ :=
  |(Pr[= true | p]).toReal - (Pr[= true | q]).toReal|

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

lemma ProbComp.distAdvantage_comm (p q : ProbComp Unit) : p.distAdvantage q = q.distAdvantage p := by
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
The experiment is considered successful unless it terminates with `failure`. -/
structure SecExp (m : Type → Type w)
    extends ExecutionMethod m where
  main : m Unit

namespace SecExp

variable {m : Type → Type w}

section advantage

noncomputable def advantage [Monad m] [HasEvalSPMF m] (exp : SecExp m) : ℝ≥0∞ :=
  1 - Pr[⊥ | exp.main]

@[simp]
lemma advantage_eq_zero_iff [Monad m] [HasEvalSPMF m] (exp : SecExp m) :
    exp.advantage = 0 ↔ Pr[⊥ | exp.main] = 1 := by
  rw [advantage, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm probFailure_le_one h, fun h => h ▸ le_refl _⟩

@[simp]
lemma advantage_eq_one_iff [Monad m] [HasEvalSPMF m] (exp : SecExp m) :
    exp.advantage = 1 ↔ Pr[⊥ | exp.main] = 0 := by
  constructor
  · intro h; by_contra hne
    have : exp.advantage < 1 := by
      unfold advantage; exact ENNReal.sub_lt_self one_ne_top one_ne_zero hne
    exact absurd h (ne_of_lt this)
  · intro h; simp [advantage, h]

end advantage

end SecExp
