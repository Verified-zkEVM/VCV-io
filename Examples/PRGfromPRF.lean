/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.PRG

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

We set up the construction and the reduction; the proof bodies remain `sorry`
for now.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal PRFScheme PRGScheme
open List (Vector)

namespace PRGfromPRF

variable {K S O : Type}
variable [Inhabited K] [Fintype K] [SampleableType K]
variable [Inhabited S] [Fintype S] [DecidableEq S] [SampleableType S]
variable [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O]

instance instSampleableTypeListVector (n : ℕ) : SampleableType (List.Vector O n) := by
  let e : (Fin n → O) ≃ List.Vector O n :=
    { toFun := List.Vector.ofFn
      invFun := fun xs i => xs.get i
      left_inv := by
        intro f
        funext i
        simp
      right_inv := by
        intro xs
        apply List.Vector.ext
        intro i
        simp }
  exact SampleableType.ofEquiv e

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

/-- In the real world, the stream PRG experiment has the same output distribution as
the real PRF experiment for the reduction adversary, provided the PRF key
distribution is uniform. -/
theorem prgRealExp_eq_prfRealExp
    (hkey : evalDist prf.keygen = evalDist ($ᵗ K : ProbComp K))
    (adv : PRGAdversary (List.Vector O n)) :
    evalDist (PRGScheme.prgRealExp (streamPRG prf n) adv) =
      evalDist (PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)) := by
  sorry

/-- In the ideal world, the reduction adversary only differs from an ideal PRG adversary
when the iterated state chain queries the same state twice. -/
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
  sorry

end streamPRG

end PRGfromPRF
