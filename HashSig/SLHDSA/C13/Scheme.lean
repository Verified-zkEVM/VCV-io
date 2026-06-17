/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.C13.ForsC
import HashSig.SLHDSA.C13.Hypertree

/-!
# C13 scheme (composition)

The top-level C13 signature, composing FORS+C with the `d = 2` hypertree. The message digest is
the 256-bit `keccak256` value `H_msg(R, PK.seed, PK.root, M)`; the FORS+C indices are its low
`a`-bit slices and the hypertree index `htIdx` is the slice at bit offset `k·a` (LSB-first,
matching `SPHINCs-C13Asm.sol`). `slhVerifyInternal` checks the FORS+C forced-zero gate and that
the hypertree reconstructs the public root.

`slhVerifyInternal_slhSignInternal` proves verification of an honestly generated signature
succeeds, **given the forced-zero grind condition** (the message randomizer is ground so the last
FORS index is `0`). It composes FORS+C correctness (`forsCPkFromSig_forsCSign`) with hypertree
correctness (`htVerify_htSign`). The signing counters are inputs (found by the WOTS+C grind); a
full `SignatureAlg` instance with a grind model, the per-layer WOTS+C digit-sum gates in
verification, and the keccak/32-byte-`ADRS` concrete instantiation + KAT are the remaining glue.

## References

- the SPHINCs- repo verifier `src/SPHINCs-C13Asm.sol`; ePrint 2025/2203
-/


namespace SLHDSA.C13

open SLHDSA (Adrs)

/-- C13 public key. -/
structure PublicKey (prims : Primitives) where
  pkSeed : prims.PkSeed
  pkRoot : prims.Y

/-- C13 secret key (carries the public material). -/
structure SecretKey (prims : Primitives) where
  skSeed : prims.SkSeed
  skPrf : prims.SkPrf
  pkSeed : prims.PkSeed
  pkRoot : prims.Y

/-- A C13 signature: randomizer `R`, FORS+C signature, and the `d = 2` hypertree signature. -/
abbrev Signature (prims : Primitives) := prims.Y × ForsSig prims × HtSig prims

/-- The hypertree index: the `h`-bit slice of the digest at bit offset `k·a` (LSB-first). -/
def htIdxOf (digest : ℕ) : ℕ := (digest >>> (params.k * params.a)) % 2 ^ params.h

theorem htIdxOf_lt (digest : ℕ) : htIdxOf digest < 2 ^ params.h := by
  unfold htIdxOf; exact Nat.mod_lt _ (by positivity)

/-- The FORS+C base address, keyed to the bottom-layer hypertree position of the digest. -/
def forsAdrsOf (digest : ℕ) : Adrs :=
  ((layerAdrs 0 (htTree0 (htIdxOf digest))).setTypeAndClear .forsTree).setKeyPairAddress
    (htLeaf0 (htIdxOf digest))

/-- C13 internal key generation: the public root is the hypertree root. -/
def slhKeygenInternal (prims : Primitives) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) : PublicKey prims × SecretKey prims :=
  let pkRoot := htRoot prims skSeed pkSeed
  (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- C13 internal signing under WOTS+C counters `count0`/`count1` (found by grinding). -/
def slhSignInternal (prims : Primitives) (msg : List Byte) (sk : SecretKey prims)
    (addrnd : prims.Y) (count0 count1 : ℕ) : Signature prims :=
  let R := prims.PRFmsg sk.skPrf addrnd msg
  let digest := prims.Hmsg R sk.pkSeed sk.pkRoot msg
  let fAdrs := forsAdrsOf digest
  let forsPk := forsPkGen prims sk.skSeed sk.pkSeed fAdrs
  (R, forsCSign prims digest sk.skSeed sk.pkSeed fAdrs,
    htSign prims forsPk sk.skSeed sk.pkSeed (htIdxOf digest) count0 count1)

/-- C13 internal verification: forced-zero gate + hypertree root reconstruction. -/
def slhVerifyInternal (prims : Primitives) [DecidableEq prims.Y] (msg : List Byte)
    (sig : Signature prims) (pk : PublicKey prims) : Bool :=
  let digest := prims.Hmsg sig.1 pk.pkSeed pk.pkRoot msg
  let fAdrs := forsAdrsOf digest
  let forsPk := forsCPkFromSig prims sig.2.1 digest pk.pkSeed fAdrs
  forcedZeroOk digest && htVerify prims forsPk sig.2.2 pk.pkSeed (htIdxOf digest) pk.pkRoot

/-- **C13 correctness** (conditional on the three grinds): an honestly generated signature
verifies, given that signing ground (a) the message randomizer so the last FORS index is `0`
(`hfz`) and (b) each layer's WOTS+C counter so the `l` base-`w` digits sum to `targetSum`
(`hd0`/`hd1` — the verifier-side gates the grind establishes). Composes FORS+C correctness with
`d = 2` hypertree correctness. -/
theorem slhVerifyInternal_slhSignInternal (prims : Primitives) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) (count0 count1 : ℕ)
    (hfz : forsIdx (prims.Hmsg (prims.PRFmsg skPrf addrnd msg) pkSeed
      (htRoot prims skSeed pkSeed) msg) (params.k - 1) = 0)
    (hd0 : digitSum prims pkSeed
      (htWotsAdrs 0 (htIdxOf (prims.Hmsg (prims.PRFmsg skPrf addrnd msg) pkSeed
        (htRoot prims skSeed pkSeed) msg)))
      (forsPkGen prims skSeed pkSeed (forsAdrsOf (prims.Hmsg (prims.PRFmsg skPrf addrnd msg)
        pkSeed (htRoot prims skSeed pkSeed) msg))) count0 = targetSum)
    (hd1 : digitSum prims pkSeed
      (htWotsAdrs 1 (htIdxOf (prims.Hmsg (prims.PRFmsg skPrf addrnd msg) pkSeed
        (htRoot prims skSeed pkSeed) msg)))
      (xmssRoot prims skSeed pkSeed (layerAdrs 0 (htTree0 (htIdxOf
        (prims.Hmsg (prims.PRFmsg skPrf addrnd msg) pkSeed (htRoot prims skSeed pkSeed) msg)))))
      count1 = targetSum) :
    slhVerifyInternal prims msg
        (slhSignInternal prims msg (slhKeygenInternal prims skSeed skPrf pkSeed).2 addrnd
          count0 count1)
        (slhKeygenInternal prims skSeed skPrf pkSeed).1 = true := by
  simp only [slhKeygenInternal, slhSignInternal, slhVerifyInternal]
  rw [forsCPkFromSig_forsCSign prims _ skSeed pkSeed _ hfz,
    htVerify_htSign prims _ skSeed pkSeed _ count0 count1 (htIdxOf_lt _) hd0 hd1]
  simp [forcedZeroOk, hfz]

end SLHDSA.C13
