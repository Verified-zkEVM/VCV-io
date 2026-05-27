/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Hiding.Scheme

/-!
# Correctness of the Hiding Ajtai Commitment
-/

open OracleComp

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Hiding

variable {Coeff : Type u} [CommRing Coeff]

/-- Blinded Ajtai commitments are perfectly correct by construction. -/
theorem perfectlyCorrect (ring : NegacyclicRing Coeff) (rows blindCols : Nat)
    [SampleableType (PublicParams ring rows blindCols)]
    [SampleableType (Opening ring blindCols)]
    [DecidableEq (Commitment ring rows)] :
    (commitmentScheme ring rows blindCols).PerfectlyCorrect := by
  intro A _ m cd hmem
  simp only [commitmentScheme, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hmem
  obtain ⟨r, _hr, hcd⟩ := hmem
  rcases hcd with rfl
  change verify ring A m (commitWithOpening ring A m r) r = true
  simp [verify]

/-- Gadget-embedded blinded Ajtai commitments are perfectly correct by construction. -/
theorem gadgetPerfectlyCorrect (ring : NegacyclicRing Coeff) (base : Coeff)
    (rows messageDigits blindCols : Nat)
    [SampleableType (PublicParams ring rows blindCols)]
    [SampleableType (Opening ring blindCols)]
    [DecidableEq (Commitment ring rows)] :
    (gadgetCommitmentScheme ring base rows messageDigits blindCols).PerfectlyCorrect := by
  intro A _ m cd hmem
  simp only [gadgetCommitmentScheme, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hmem
  obtain ⟨r, _hr, hcd⟩ := hmem
  rcases hcd with rfl
  change
    gadgetVerify ring base A m (gadgetCommitWithOpening ring base A m r) r = true
  simp [gadgetVerify, gadgetCommitWithOpening, verify]
end Hiding
end Ajtai
end LatticeCrypto
