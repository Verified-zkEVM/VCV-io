/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple.Scheme

/-!
# Correctness of the Simple Ajtai Commitment
-/

open OracleComp
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

@[simp] theorem verify_commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols) :
    verify ring A s (commit ring A s) () = true := by
  simp [verify]

@[simp] theorem verify_eq_true_iff (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols)
    (c : Commitment ring rows) (opening : Opening) :
    verify ring A s c opening = true ↔ commit ring A s = c := by
  simp [verify]

/-- Simple Ajtai commitments are perfectly correct by construction. -/
theorem perfectlyCorrect (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Commitment ring rows)] :
    (commitmentScheme ring rows cols).PerfectlyCorrect := by
  intro A _ s cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  change verify ring A s (commit ring A s) () = true
  simp

end Simple
end Ajtai
end LatticeCrypto
