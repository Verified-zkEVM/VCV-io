/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Gadget
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Simple Ajtai Commitment

The simple Ajtai commitment over a bundled negacyclic ring.  Public parameters
are a uniformly sampled matrix `A`; committing to a vector `s` returns `A * s`
and uses the trivial opening. Non-hiding, but binding under Module-SIS.
-/

open OracleComp

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for the simple Ajtai commitment. -/
abbrev PublicParams (ring : NegacyclicRing Coeff) (rows cols : Nat) :=
  PolyMatrix ring.Poly rows cols

/-- Messages for the simple Ajtai commitment. -/
abbrev Message (ring : NegacyclicRing Coeff) (cols : Nat) :=
  PolyVec ring.Poly cols

/-- Commitments for the simple Ajtai commitment. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (rows : Nat) :=
  PolyVec ring.Poly rows

/-- Deterministically commit by multiplying the public matrix by the message vector. -/
def commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    (A : PublicParams ring rows cols) (s : Message ring cols) : Commitment ring rows :=
  ring.matVecMul A s

/-- The simple Ajtai commitment has no auxiliary opening data. -/
abbrev Opening := Unit

/-- Verify a simple Ajtai opening by checking the matrix product. -/
def verify (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols)
    (c : Commitment ring rows) (_opening : Opening) : Bool :=
  if _ : commit ring A s = c then true else false

@[simp] theorem verify_commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols) :
    verify ring A s (commit ring A s) () = true := by
  simp [verify]

/-- The simple Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening where
  setup := $ᵗ PublicParams ring rows cols
  commit A s := pure (commit ring A s, ())
  verify A s c opening := verify ring A s c opening

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
