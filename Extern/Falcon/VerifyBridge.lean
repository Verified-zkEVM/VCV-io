/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import Extern.Falcon.FPRBridge

/-!
# The concrete Falcon verifier agrees with the abstract one

`Falcon.Concrete.FPRBridge.concrete_verify_eq_verify` relates the standalone executable verifier
`concreteVerify` to the abstract `Falcon.verify` under four side conditions: the signature and
public-key codecs round-trip, and the `UInt32`/`Int64` arithmetic kernels compute the
specification-level `negacyclicMul` and `pairL2NormSq`. All four are now theorems
(`sigDecode_sigEncode`, `publicKeyBytes_extract` with `pkDecode_pkEncode`,
`negacyclicMulU32_eq_negacyclicMul`, `pairL2NormSqU32_eq_pairL2NormSq`), so the bridge holds
outright at every Falcon degree: `4 ∣ n` for the public-key packing and the `UInt64`
no-overflow bound `2 · n · (q/2)² < 2⁶⁴` for the norm accumulator, which holds with vast headroom
for `n ≤ 1024`.
-/

public section

namespace Falcon.Concrete.FPRBridge

/-- The verify bridge with its codec and kernel side conditions discharged. -/
theorem concrete_verify_eq_verify_of_dvd
    (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) (hsbytelen : 0 < p.sbytelen)
    (hn_ovf : 2 * p.n * (Falcon.modulus / 2) ^ 2 < 2 ^ 64) (hn4 : 4 ∣ p.n)
    (pk : Falcon.PublicKey p) (msg : List Falcon.Byte) (sig : Falcon.Signature) :
    let prims := verifyPrimitives p hn;
    Falcon.Concrete.concreteVerify p (prims.publicKeyBytes pk.h) msg
      (Falcon.Concrete.sigEncode sig.salt sig.compressedS2 p.logn) =
        Falcon.verify p prims pk msg sig :=
  concrete_verify_eq_verify p hn hsbytelen
    (fun salt compSig hne => Falcon.Concrete.sigDecode_sigEncode salt compSig p.logn hne)
    (fun h => by
      rw [Falcon.Concrete.publicKeyBytes_extract, Falcon.Concrete.pkDecode_pkEncode p.n h hn4])
    (fun s2 h => Falcon.Concrete.negacyclicMulU32_eq_negacyclicMul s2 h)
    (fun s1 s2 => Falcon.Concrete.pairL2NormSqU32_eq_pairL2NormSq hn_ovf s1 s2) pk msg sig

/-- At every Falcon degree `n = 2 ^ logn` with `2 ≤ logn ≤ 10`, both side conditions of
`concrete_verify_eq_verify_of_dvd` hold, so the concrete and abstract verifiers agree. -/
theorem concrete_verify_eq_verify_of_logn
    (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) (hsbytelen : 0 < p.sbytelen)
    (hlo : 2 ≤ p.logn) (hhi : p.logn ≤ 10)
    (pk : Falcon.PublicKey p) (msg : List Falcon.Byte) (sig : Falcon.Signature) :
    let prims := verifyPrimitives p hn;
    Falcon.Concrete.concreteVerify p (prims.publicKeyBytes pk.h) msg
      (Falcon.Concrete.sigEncode sig.salt sig.compressedS2 p.logn) =
        Falcon.verify p prims pk msg sig := by
  have hle : p.n ≤ 1024 := by
    rw [hn]
    calc 2 ^ p.logn ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hhi
      _ = 1024 := by norm_num
  have hn_ovf : 2 * p.n * (Falcon.modulus / 2) ^ 2 < 2 ^ 64 := by
    have : (Falcon.modulus / 2) ^ 2 = 6144 ^ 2 := by norm_num [Falcon.modulus]
    rw [this]
    calc 2 * p.n * 6144 ^ 2 ≤ 2 * 1024 * 6144 ^ 2 := by gcongr
      _ < 2 ^ 64 := by norm_num
  have hn4 : 4 ∣ p.n := by
    rw [hn]
    exact (pow_dvd_pow 2 hlo).trans (by norm_num)
  exact concrete_verify_eq_verify_of_dvd p hn hsbytelen hn_ovf hn4 pk msg sig

end Falcon.Concrete.FPRBridge

end
