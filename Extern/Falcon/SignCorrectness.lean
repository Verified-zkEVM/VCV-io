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

/-!
# Verification correctness at the concrete Falcon primitives

`Falcon.verify_sign_correct` takes two facts about the primitives: the codec round-trips and the
trapdoor sampler lands on the coset. At `Falcon.Concrete.FPRBridge.verifyPrimitives` and
`Falcon.Concrete.concretePrimitives` the codec is the concrete Golomb-Rice codec, whose round-trip
`Falcon.Concrete.decompress_compress` is a theorem, so only the coset condition `hpreimage`
remains: the lattice-point obligation of the floating-point inverse FFT.
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

end Falcon.Concrete

end
