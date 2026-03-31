/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.PRG
import VCVio.EvalDist.TVDist

/-!
# PRG from PRF

This file constructs a simple stream-style PRG from a PRF
`f : K → S → S × O`. Starting from a random state `s₀`, each round applies
the PRF to the current state, producing the next state and one output block.

The proof outline follows the standard switching argument:

1. Replace the real PRF with a random function.
2. Show that, except when the state chain repeats, the random-function world is
   identical to the ideal PRG world of independent uniform outputs.
3. Bound the remaining gap by the probability of a state collision.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open OracleComp OracleSpec ENNReal PRFScheme PRGScheme
open List (Vector)

namespace PRGfromPRF

variable {K S O : Type}
variable [Inhabited K] [Fintype K] [SampleableType K]
variable [Inhabited S] [Fintype S] [DecidableEq S] [SampleableType S]
variable [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O]

instance instSampleableTypeListVector (n : ℕ) : SampleableType (List.Vector O n) :=
  SampleableType.ofEquiv
    { toFun := List.Vector.ofFn
      invFun := fun xs i => xs.get i
      left_inv := fun f => funext fun i => by simp
      right_inv := fun xs => List.Vector.ext fun i => by simp }

/-- Deterministically unroll `n` rounds of a state transition/output function. -/
def streamOutputs (step : S → S × O) : (n : ℕ) → S → List.Vector O n
  | 0, _ => .nil
  | n + 1, s =>
      let (s', out) := step s
      out ::ᵥ streamOutputs step n s'

/-- Query the PRF oracle `n` times, threading the returned state and collecting outputs. -/
def oracleOutputs :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector O n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', out) ← query (spec := PRFScheme.PRFOracleSpec S (S × O)) (Sum.inr s)
      let rest ← oracleOutputs n s'
      pure (out ::ᵥ rest)

/-- Query the PRF oracle `n` times, recording the states fed to the oracle. Repeated
states are exactly the bad event for the random-function to ideal-PRG hop. -/
def oracleVisitedStates :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector S n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', _) ← query (spec := PRFScheme.PRFOracleSpec S (S × O)) (Sum.inr s)
      let rest ← oracleVisitedStates n s'
      pure (s ::ᵥ rest)

/-- Stream-style PRG obtained by iterating a PRF `n` times. The seed contains both the
PRF key and the initial state; later theorems assume the PRF key distribution is uniform. -/
@[simps!] def streamPRG (prf : PRFScheme K S (S × O)) (n : ℕ) :
    PRGScheme (K × S) (List.Vector O n) where
  gen ks := streamOutputs (prf.eval ks.1) n ks.2

namespace streamPRG

variable {prf : PRFScheme K S (S × O)} {n : ℕ}

/-- Reduction from a distinguisher on the stream PRG output to a PRF distinguisher. It
samples an initial state, queries the candidate oracle `n` times, and feeds the resulting
output vector to the PRG adversary. -/
def prfReduction (n : ℕ) (adv : PRGAdversary (List.Vector O n)) : PRFAdversary S (S × O) :=
  show OracleComp (unifSpec + (S →ₒ S × O)) Bool from do
    let seed ← OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (S →ₒ S × O))
      ($ᵗ S : ProbComp S)
    let outputs ← oracleOutputs n seed
    OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (S →ₒ S × O))
      (adv outputs)

/-- Collision experiment for the ideal random-function world: sample an initial state,
iterate a lazy random oracle for `n` rounds, and test whether any queried state repeats. -/
def idealCollisionExp (n : ℕ) : ProbComp Bool := do
  let seed ← $ᵗ S
  let states ←
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := S) (R := S × O))
      (oracleVisitedStates n seed)).run' ∅
  return decide (¬ states.toList.Nodup)

/-- Probability of the bad event in the ideal random-function world. -/
noncomputable def collisionProb (n : ℕ) : ℝ :=
  (Pr[= true | idealCollisionExp (S := S) (O := O) n]).toReal

/-- Under the real PRF query implementation, querying the oracle `n` times produces the
same outputs as the deterministic `streamOutputs`. -/
private lemma simulateQ_prfReal_oracleOutputs (k : K) (n : ℕ) (s : S) :
    simulateQ (prfRealQueryImpl prf k) (oracleOutputs n s) =
      (pure (streamOutputs (prf.eval k) n s) : ProbComp _) := by
  induction n generalizing s with
  | zero => simp [oracleOutputs, streamOutputs]
  | succ n ih =>
    simp only [oracleOutputs, streamOutputs, simulateQ_bind, simulateQ_query,
      OracleQuery.cont_query, id_map, OracleQuery.input_query]
    show prfRealQueryImpl prf k (Sum.inr s) >>= _ = _
    simp only [prfRealQueryImpl, QueryImpl.add_apply_inr, pure_bind, simulateQ_bind,
      simulateQ_pure]
    change (do let x ← simulateQ (prfRealQueryImpl prf k)
                  (oracleOutputs n (prf.eval k s).1)
               pure ((prf.eval k s).2 ::ᵥ x)) = _
    rw [ih]; simp

/-- Applying the real PRF query implementation to the full reduction body simplifies to
sampling a seed and running the adversary on deterministic output. -/
private lemma simulateQ_prfReal_reduction (k : K) (n : ℕ)
    (adv : PRGAdversary (List.Vector O n)) :
    simulateQ (prf.prfRealQueryImpl k)
      (show OracleComp (unifSpec + (S →ₒ S × O)) Bool from do
        let seed ← liftComp ($ᵗ S) (unifSpec + ofFn fun _ => S × O)
        let outputs ← oracleOutputs n seed
        liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
    (do let s ← $ᵗ S; adv (streamOutputs (prf.eval k) n s)) := by
  simp only [simulateQ_bind]
  have h1 : simulateQ (prf.prfRealQueryImpl k)
      (liftComp ($ᵗ S) (unifSpec + ofFn fun _ => S × O)) = ($ᵗ S : ProbComp S) := by
    simp only [prfRealQueryImpl]; rw [QueryImpl.simulateQ_add_liftComp_left]
    exact simulateQ_ofLift_eq_self _
  rw [h1]; congr 1; funext s
  rw [simulateQ_prfReal_oracleOutputs, pure_bind, prfRealQueryImpl,
    QueryImpl.simulateQ_add_liftComp_left]; exact simulateQ_ofLift_eq_self _

/-- In the real world, the stream PRG experiment has the same output distribution as
the real PRF experiment for the reduction adversary, provided the PRF key
distribution is uniform. -/
theorem prgRealExp_eq_prfRealExp
    (hkey : evalDist prf.keygen = evalDist ($ᵗ K : ProbComp K))
    (adv : PRGAdversary (List.Vector O n)) :
    evalDist (PRGScheme.prgRealExp (streamPRG prf n) adv) =
      evalDist (PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)) := by
  simp only [PRGScheme.prgRealExp, PRFScheme.prfRealExp, prfReduction, streamPRG]
  simp_rw [simulateQ_prfReal_reduction]
  change evalDist ((·, ·) <$> ($ᵗ K) <*> ($ᵗ S) >>=
    fun ks => adv (streamOutputs (prf.eval ks.1) n ks.2)) = _
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rw [evalDist_bind, evalDist_bind, hkey]

/-- The gap between the ideal PRF and ideal PRG experiments is bounded by the
collision probability. This follows from the fundamental lemma of game playing:
when a lazy random function never receives the same input twice, its outputs are
independent uniform — matching the ideal PRG distribution exactly. The bound
comes from the probability that the state chain revisits some state.

*Proof outline (switching argument):*
1. Factor both experiments as: sample inputs to `adv`, then run `adv`.
2. In the ideal PRF world, the inputs come from a random-oracle chain.
3. In the ideal PRG world, the inputs are i.i.d. uniform.
4. Conditioned on no state collision, the random-oracle chain produces
   independent uniform outputs, so the two input distributions coincide.
5. By the "identical until bad" lemma (`tvDist_simulateQ_le_probEvent_bad`),
   the TV distance between the two input distributions is at most `Pr[collision]`.
6. By the data-processing inequality, running `adv` cannot increase the gap.

Full formalization requires coupling the random-oracle chain with independent
uniform outputs and instantiating the switching-lemma infrastructure for this
specific oracle. -/
theorem prfIdealGap_le_collisionProb (adv : PRGAdversary (List.Vector O n)) :
    |(Pr[= true | PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv)]).toReal -
      (Pr[= true | PRGScheme.prgIdealExp adv]).toReal| ≤
      collisionProb (S := S) (O := O) n := by
  sorry

/-- Security of the stream PRG obtained from a PRF: PRG distinguishing advantage is
bounded by the PRF advantage of the reduction plus the collision probability in the
ideal random-function world. -/
theorem security
    (hkey : evalDist prf.keygen = evalDist ($ᵗ K : ProbComp K))
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
      collisionProb (S := S) (O := O) n := by
  unfold PRGScheme.prgAdvantage PRFScheme.prfAdvantage
  have hreal : (Pr[= true | PRGScheme.prgRealExp (streamPRG prf n) adv]).toReal =
      (Pr[= true | PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)]).toReal :=
    congrArg ENNReal.toReal (probOutput_congr rfl (prgRealExp_eq_prfRealExp hkey adv))
  rw [hreal]
  set a := (Pr[= true | PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)]).toReal
  set b := (Pr[= true | PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv)]).toReal
  set c := (Pr[= true | PRGScheme.prgIdealExp adv]).toReal
  have hgap : |b - c| ≤ collisionProb (S := S) (O := O) n :=
    prfIdealGap_le_collisionProb adv
  calc |a - c| = |(a - b) + (b - c)| := by ring_nf
    _ ≤ |a - b| + |b - c| := abs_add_le _ _
    _ ≤ |a - b| + collisionProb (S := S) (O := O) n := by linarith

end streamPRG

end PRGfromPRF
