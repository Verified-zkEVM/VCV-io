/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.HypertreeGeneral.QueryBound

/-!
# Query bounds for general internal SLH-DSA

Closed public-hash budgets for FIPS 205 Algorithms 18--20 at arbitrary hypertree depth `d`.
Signature widths are intrinsic, so verification bounds are independent of attacker-controlled
list lengths.
-/

@[expose] public section

namespace SLHDSA.GeneralScheme

open OracleComp

variable {p : Params}

/-- Algorithm 18 computes one top-layer XMSS root. -/
def keygenInternalQueryBound (p : Params) : ℕ :=
  xmssNodeQueryBound p p.hp

/-- Algorithm 19: `H_msg`, honest FORS signing and recovery, then arbitrary-`d` hypertree
signing. -/
def signInternalQueryBound (p : Params) : ℕ :=
  1 + (p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1)) +
      (p.k * (p.a + 1) + 1)) +
    GeneralHypertree.signQueryBound p

/-- Algorithm 20: `H_msg`, intrinsic FORS recovery, and `d` intrinsic XMSS recoveries. -/
def verifyInternalQueryBound (p : Params) : ℕ :=
  1 + (p.k * (p.a + 1) + 1) + GeneralHypertree.recoverQueryBound p

private theorem publicHash_hmsg_isTotalQueryBound_one (core : CorePrimitives p)
    (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    IsTotalQueryBound
      (PublicHash.hmsg core r pkSeed pkRoot msg :
        OracleComp (publicHashSpec core) (Bytes p.m)) 1 := by
  simp [PublicHash.hmsg, IsTotalQueryBound]

theorem keygenInternalM_isTotalQueryBound (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (skSeed : core.SkSeed) (skPrf : core.SkPrf)
    (pkSeed : core.PkSeed) :
    IsTotalQueryBound
      (keygenInternalM vp core skSeed skPrf pkSeed :
        OracleComp (publicHashSpec core) (PublicKeyCore core × SecretKeyCore core))
      (keygenInternalQueryBound vp.params) := by
  simpa [keygenInternalM, keygenInternalQueryBound, GeneralHypertree.rootM,
    GeneralHypertree.rootWith, xmssRootM] using
    isTotalQueryBound_bind
      (xmssRootM_isTotalQueryBound core skSeed pkSeed
        (GeneralHypertree.layerAdrs (vp.params.d - 1) 0))
      (fun pkRoot => show IsTotalQueryBound
        (pure (PublicKeyCore.mk pkSeed pkRoot,
          SecretKeyCore.mk skSeed skPrf pkSeed pkRoot) :
          OracleComp (publicHashSpec core) _) 0 from trivial)

theorem signInternalM_isTotalQueryBound (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (msg : List Byte) (sk : SecretKeyCore core)
    (addrnd : core.Y) :
    IsTotalQueryBound
      (signInternalM vp core msg sk addrnd :
        OracleComp (publicHashSpec core) (SignatureCore vp core))
      (signInternalQueryBound vp.params) := by
  let R := core.PRFmsg sk.skPrf addrnd msg
  have hbound := isTotalQueryBound_bind
    (publicHash_hmsg_isTotalQueryBound_one core R sk.pkSeed sk.pkRoot msg) fun digest =>
      let parts := splitDigest vp.params digest
      isTotalQueryBound_bind
        (forsSignM_then_forsPkFromSigM_isTotalQueryBound
          core parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs) fun sigAndPk =>
            isTotalQueryBound_bind
              (GeneralHypertree.signM_isTotalQueryBound vp core sigAndPk.2
                sk.skSeed sk.pkSeed parts) fun htSig =>
                  show IsTotalQueryBound
                    (pure (SignatureCore.mk R sigAndPk.1 htSig) :
                      OracleComp (publicHashSpec core) (SignatureCore vp core)) 0 from trivial
  simpa [signInternalM, signInternalQueryBound, R, bind_assoc, Nat.add_assoc] using hbound

theorem verifyInternalM_isTotalQueryBound (vp : ValidatedParams)
    (core : CorePrimitives vp.params) [DecidableEq core.Y]
    (msg : List Byte) (sig : SignatureCore vp core) (pk : PublicKeyCore core) :
    IsTotalQueryBound
      (verifyInternalM vp core msg sig pk : OracleComp (publicHashSpec core) Bool)
      (verifyInternalQueryBound vp.params) := by
  have hbound := isTotalQueryBound_bind
    (publicHash_hmsg_isTotalQueryBound_one core sig.randomness pk.pkSeed pk.pkRoot msg)
    fun digest =>
      let parts := splitDigest vp.params digest
      isTotalQueryBound_bind
        (forsPkFromSigM_isTotalQueryBound core sig.fors parts.md.toList pk.pkSeed
          parts.forsAdrs) fun forsPk =>
            isTotalQueryBound_bind
              (GeneralHypertree.pkFromSigM_isTotalQueryBound vp core forsPk sig.hypertree
                pk.pkSeed parts) fun recovered =>
                  show IsTotalQueryBound
                    (pure (decide (recovered = pk.pkRoot)) :
                      OracleComp (publicHashSpec core) Bool) 0 from trivial
  simpa [verifyInternalM, GeneralHypertree.verifyM, verifyInternalQueryBound,
    bind_assoc, Nat.add_assoc] using hbound

end SLHDSA.GeneralScheme
