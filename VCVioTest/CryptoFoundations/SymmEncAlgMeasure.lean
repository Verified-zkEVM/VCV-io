/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module


public import VCVio.CryptoFoundations.SymmEncAlg.MeasureCompatibility

/-!
# Symmetric-encryption measure canaries

The negative canary below is deliberately branch-distinguishing: an encryption channel that
reveals its Boolean message has unequal measure rows and therefore cannot satisfy measure-level
perfect secrecy.
-/

public section

open MeasureTheory

namespace SymmEncAlg.MeasureTest

/-- Dirac semantics for deterministic identity computations. -/
noncomputable def idSemantics : ProbabilitySemantics Id where
  denote value := Measure.dirac value
  apply_univ_le_one value := by simp
  isProbabilityMeasure value := inferInstance

/-- An intentionally insecure Boolean channel: the ciphertext is exactly the message. -/
def identityChannel : SymmEncAlg Id Bool Unit Bool where
  keygen := ()
  encrypt _ message := message
  decrypt _ ciphertext := some ciphertext

/-- The two channel rows are genuinely different, so the secrecy predicate detects the leak. -/
theorem identityChannel_not_measurePerfectSecrecyAt :
    ¬ identityChannel.measurePerfectSecrecyAt idSemantics := by
  intro hsecrecy
  have hrows := hsecrecy false true
  change Measure.dirac false = Measure.dirac true at hrows
  have hfalse := congrArg (fun μ : Measure Bool ↦ μ {false}) hrows
  simp at hfalse

end SymmEncAlg.MeasureTest
