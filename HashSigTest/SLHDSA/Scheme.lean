/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Scheme

/-!
# Oracle-parametric SLH-DSA scheme canaries

These examples cover the two observable internal FIPS 205 schedules. Signing performs `H_msg`,
FORS signing, recovery from that exact signature, and hypertree signing in order; it never
regenerates the FORS public key.
-/

public section

namespace SLHDSA.SchemeTest

open OracleComp

variable {p : Params} (hd : p.d = 1) (core : CorePrimitives p)

/-- FIPS 205 Algorithm 19 recovers the FORS public key from the generated signature before
hypertree signing. Replacing that recovery with `forsPkGenM` makes this canary fail. -/
example (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) :
    (slhSignInternalM hd core msg sk addrnd :
      OracleComp (publicHashSpec core) (SignatureCore p core)) = (do
        let R := core.PRFmsg sk.skPrf addrnd msg
        let digest ← PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg
        let parts := splitDigest p digest
        let forsSig ← forsSignM core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs
        let forsPk ←
          forsPkFromSigM core forsSig parts.md.toList sk.pkSeed parts.forsAdrs
        let htSig ← htSignM core hd forsPk sk.skSeed sk.pkSeed Adrs.zero 0 parts.idxLeaf.val
        return ⟨R, forsSig, htSig⟩) := by
  rfl

/-- Verification performs `H_msg`, FORS recovery, and hypertree recovery/comparison in order. -/
example [DecidableEq core.Y] (msg : List Byte) (sig : SignatureCore p core)
    (pk : PublicKeyCore core) :
    (slhVerifyInternalM hd core msg sig pk : OracleComp (publicHashSpec core) Bool) = (do
      let digest ← PublicHash.hmsg core sig.randomness pk.pkSeed pk.pkRoot msg
      let parts := splitDigest p digest
      let forsPk ← forsPkFromSigM core sig.fors parts.md.toList pk.pkSeed parts.forsAdrs
      htVerifyM core hd forsPk sig.hypertree pk.pkSeed Adrs.zero 0 parts.idxLeaf.val
        pk.pkRoot) := by
  rfl

end SLHDSA.SchemeTest
