/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
import all Extern.Falcon.Instance
import all Extern.Falcon.FPRBridge
public import Extern.Falcon.FPRBridge
public import LatticeCrypto.Falcon.Security
public import LatticeCrypto.Falcon.Coset

/-!
# Verification correctness at the concrete Falcon primitives

`Falcon.verify_sign_correct` takes two facts about the primitives: the codec round-trips and the
trapdoor sampler lands on the coset. At `Falcon.Concrete.FPRBridge.verifyPrimitives` and
`Falcon.Concrete.concretePrimitives` the codec is the concrete Golomb-Rice codec, whose round-trip
`Falcon.Concrete.decompress_compress` is a theorem, so only the coset condition `hpreimage`
remains. `Falcon.hpreimage_of_landsOnLattice` reduces that condition further, to the
lattice-point condition `Falcon.LandsOnLattice` on the fixed-point FFT pipeline together with
the key relations; the `_of_landsOnLattice` variants below take only those.
-/

public section

open OracleComp OracleSpec Falcon

namespace Falcon.Concrete

/-- Verification correctness at the FPR-backed verification primitives, given only that the
trapdoor sampler lands on the coset. -/
theorem verify_sign_correct_verifyPrimitives
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hpreimage : ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p (FPRBridge.verifyPrimitives p hn)).trapdoorSample pk sk c) →
        (falconPSF p (FPRBridge.verifyPrimitives p hn)).eval pk x = c)
    (hsig : some sig ∈ support (sign p (FPRBridge.verifyPrimitives p hn) pk sk msg maxAttempts)) :
    verify p (FPRBridge.verifyPrimitives p hn) pk msg sig = true :=
  verify_sign_correct p (FPRBridge.verifyPrimitives p hn) pk sk msg maxAttempts sig
    (fun s slen bytes h => decompress_compress p.n s slen bytes h) hpreimage hsig

/-- Verification correctness at the concrete primitives bundle, given only that the trapdoor
sampler lands on the coset. -/
theorem verify_sign_correct_concretePrimitives
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hpreimage : ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p (concretePrimitives p hn)).trapdoorSample pk sk c) →
        (falconPSF p (concretePrimitives p hn)).eval pk x = c)
    (hsig : some sig ∈ support (sign p (concretePrimitives p hn) pk sk msg maxAttempts)) :
    verify p (concretePrimitives p hn) pk msg sig = true :=
  verify_sign_correct p (concretePrimitives p hn) pk sk msg maxAttempts sig
    (fun s slen bytes h => decompress_compress p.n s slen bytes h) hpreimage hsig

/-- Verification correctness at the concrete primitives bundle from key validity, invertibility
of `f` modulo `q`, and the lattice-point condition on the fixed-point FFT pipeline. -/
theorem verify_sign_correct_concretePrimitives_of_landsOnLattice
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1)
    (hz : ∀ c : Rq p.n, ∀ z ∈ support (Primitives.ffSampling (concretePrimitives p hn)
      p.fftDepth (toFFTTarget p (concretePrimitives p hn) c sk) sk.tree),
      LandsOnLattice p (concretePrimitives p hn) sk z)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign p (concretePrimitives p hn) pk sk msg maxAttempts)) :
    verify p (concretePrimitives p hn) pk msg sig = true := by
  have hpos : 0 < p.n := by rw [hn]; positivity
  have hkey := (validKeyPair_eq_true_iff p pk sk).mp hvalid |>.2
  exact verify_sign_correct_concretePrimitives p hn pk sk msg maxAttempts sig
    (hpreimage_of_landsOnLattice p (concretePrimitives p hn) hpos pk sk hkey
      (capRelation_of_validKeyPair p hpos pk sk hvalid hunit) hz) hsig

/-- The same at the FPR-backed verification primitives. -/
theorem verify_sign_correct_verifyPrimitives_of_landsOnLattice
    (p : Params) (hn : p.n = 2 ^ p.logn) (pk : PublicKey p) (sk : SecretKey p)
    (hvalid : validKeyPair p pk sk = true)
    (hunit : ∃ u : Rq p.n, negacyclicMul (IntPoly.toRq sk.f) u = 1)
    (hz : ∀ c : Rq p.n, ∀ z ∈ support (Primitives.ffSampling (FPRBridge.verifyPrimitives p hn)
      p.fftDepth (toFFTTarget p (FPRBridge.verifyPrimitives p hn) c sk) sk.tree),
      LandsOnLattice p (FPRBridge.verifyPrimitives p hn) sk z)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support
      (sign p (FPRBridge.verifyPrimitives p hn) pk sk msg maxAttempts)) :
    verify p (FPRBridge.verifyPrimitives p hn) pk msg sig = true := by
  have hpos : 0 < p.n := by rw [hn]; positivity
  have hkey := (validKeyPair_eq_true_iff p pk sk).mp hvalid |>.2
  exact verify_sign_correct_verifyPrimitives p hn pk sk msg maxAttempts sig
    (hpreimage_of_landsOnLattice p (FPRBridge.verifyPrimitives p hn) hpos pk sk hkey
      (capRelation_of_validKeyPair p hpos pk sk hvalid hunit) hz) hsig

end Falcon.Concrete

end
