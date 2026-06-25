/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Hypertree
import VCVio.CryptoFoundations.SignatureAlg

/-!
# SLH-DSA Scheme (FIPS 205 §9–10)

The top-level SLH-DSA signature scheme for the `d = 1` parameter set, assembled from FORS
(`HashSig.SLHDSA.Fors`) and the single-layer hypertree (`HashSig.SLHDSA.Hypertree`):

- `slhKeygenInternal` / `slhSignInternal` / `slhVerifyInternal` (Algorithms 18–20),
- `splitDigest`, the message-digest split into `(md, idxLeaf)` (§9; for `d = 1` the tree index
  is always `0`, so it is omitted),
- the external probabilistic wrappers `slhKeygen` / `slhSign` / `slhVerify` (Algorithms 21–24,
  empty context), and the generic `SignatureAlg` instantiation `slhdsaAlg` in `ProbComp`.

The headline result `slhdsaAlg_perfectlyComplete` proves **perfect completeness with no `sorry`**:
every honestly generated signature verifies. It is a deterministic hash-tree consistency fact
(`slhVerifyInternal_slhSignInternal`) composing WOTS+/XMSS/FORS/hypertree correctness, lifted
across the sampling of seeds via the support characterization of `Pr[… ] = 1`.

## References

- NIST FIPS 205, §9 (Algorithms 18–22, 24), §10 (external API), §4.1 (the H_msg digest split)
-/


open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}

/-- The SLH-DSA public key: public seed and hypertree root. -/
structure PublicKey (prims : Primitives p) where
  /-- Public seed `PK.seed`. -/
  pkSeed : prims.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : prims.Y

/-- The SLH-DSA secret key: it carries the public material for signing. -/
structure SecretKey (prims : Primitives p) where
  /-- Secret seed `SK.seed`. -/
  skSeed : prims.SkSeed
  /-- Message-PRF key `SK.prf`. -/
  skPrf : prims.SkPrf
  /-- Public seed `PK.seed`. -/
  pkSeed : prims.PkSeed
  /-- Hypertree root `PK.root`. -/
  pkRoot : prims.Y

/-- An SLH-DSA signature: randomizer `R`, FORS signature, and hypertree signature
(`R ‖ SIG_FORS ‖ SIG_HT`). -/
abbrev Signature (prims : Primitives p) := prims.Y × ForsSig p prims × HtSig p prims

/-! ### Message-digest split (FIPS 205 §9) -/

/-- Split the message digest into the FORS message `md` and the hypertree leaf index `idxLeaf`
(reduced mod `2^{h'}`). For `d = 1` the tree-index field is empty, so the tree index is `0` and
omitted. -/
def splitDigest (p : Params) (digest : Bytes p.m) : List Byte × ℕ :=
  let bytes := digest.toList
  (bytes.take p.digestBytes,
    toInt ((bytes.drop (p.digestBytes + p.treeIdxBytes)).take p.leafIdxBytes) % 2 ^ p.hp)

theorem splitDigest_snd_lt (p : Params) (digest : Bytes p.m) :
    (splitDigest p digest).2 < 2 ^ p.hp := by
  simp only [splitDigest]
  exact Nat.mod_lt _ (by positivity)

/-- The FORS base address keyed to the per-message hypertree leaf `idxLeaf` (FIPS 205 Alg 19). -/
def forsAdrsOf (idxLeaf : ℕ) : Adrs :=
  ((Adrs.zero.setTreeAddress 0).setTypeAndClear .forsTree).setKeyPairAddress idxLeaf

/-! ### Internal algorithms (FIPS 205 §9) -/

/-- SLH-DSA internal key generation (FIPS 205 Algorithm 18): the public root is the hypertree
root of the single tree. -/
def slhKeygenInternal (prims : Primitives p) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) : PublicKey prims × SecretKey prims :=
  let pkRoot := htRoot prims skSeed pkSeed Adrs.zero 0
  (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

/-- SLH-DSA internal signing (FIPS 205 Algorithm 19): derive `R` and the digest, sign the FORS
public key with the hypertree. -/
def slhSignInternal (prims : Primitives p) (msg : List Byte) (sk : SecretKey prims)
    (addrnd : prims.Y) : Signature prims :=
  let R := prims.PRFmsg sk.skPrf addrnd msg
  let digest := prims.Hmsg R sk.pkSeed sk.pkRoot msg
  let idxLeaf := (splitDigest p digest).2
  let md := (splitDigest p digest).1
  let fAdrs := forsAdrsOf idxLeaf
  (R, forsSign prims md sk.skSeed sk.pkSeed fAdrs,
    htSign prims (forsPkGen prims sk.skSeed sk.pkSeed fAdrs) sk.skSeed sk.pkSeed Adrs.zero 0
      idxLeaf)

/-- SLH-DSA internal verification (FIPS 205 Algorithm 20): recompute the FORS public key and
verify it against the hypertree. -/
def slhVerifyInternal (prims : Primitives p) [DecidableEq prims.Y] (msg : List Byte)
    (sig : Signature prims) (pk : PublicKey prims) : Bool :=
  let digest := prims.Hmsg sig.1 pk.pkSeed pk.pkRoot msg
  let idxLeaf := (splitDigest p digest).2
  let md := (splitDigest p digest).1
  let fAdrs := forsAdrsOf idxLeaf
  htVerify prims (forsPkFromSig prims sig.2.1 md pk.pkSeed fAdrs) sig.2.2 pk.pkSeed Adrs.zero 0
    idxLeaf pk.pkRoot

/-- **Deterministic correctness core**: an honestly generated signature verifies, for every
choice of seeds and randomizer. Composes FORS correctness (`forsPkFromSig_forsSign`) with
hypertree correctness (`htVerify_htSign`). -/
theorem slhVerifyInternal_slhSignInternal (prims : Primitives p) [DecidableEq prims.Y]
    (msg : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed)
    (addrnd : prims.Y) :
    slhVerifyInternal prims msg
        (slhSignInternal prims msg (slhKeygenInternal prims skSeed skPrf pkSeed).2 addrnd)
        (slhKeygenInternal prims skSeed skPrf pkSeed).1 = true := by
  simp only [slhKeygenInternal, slhSignInternal, slhVerifyInternal]
  rw [forsPkFromSig_forsSign]
  exact htVerify_htSign prims _ skSeed pkSeed Adrs.zero 0 _ (splitDigest_snd_lt p _)

/-! ### External algorithms and the `SignatureAlg` instance (FIPS 205 §10) -/

variable (prims : Primitives p)

/-- SLH-DSA key generation (FIPS 205 Algorithm 21): sample the three seeds. -/
def slhKeygen [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] : ProbComp (PublicKey prims × SecretKey prims) := do
  let skSeed ← $ᵗ prims.SkSeed
  let skPrf ← $ᵗ prims.SkPrf
  let pkSeed ← $ᵗ prims.PkSeed
  return slhKeygenInternal prims skSeed skPrf pkSeed

/-- SLH-DSA signing (FIPS 205 Algorithm 22, empty context, hedged): sample `addrnd`. -/
def slhSign [SampleableType prims.Y] (sk : SecretKey prims) (msg : List Byte) :
    ProbComp (Signature prims) := do
  let addrnd ← $ᵗ prims.Y
  return slhSignInternal prims msg sk addrnd

/-- SLH-DSA verification (FIPS 205 Algorithm 24, empty context). -/
def slhVerify [DecidableEq prims.Y] (pk : PublicKey prims) (msg : List Byte)
    (sig : Signature prims) : Bool :=
  slhVerifyInternal prims msg sig pk

/-- SLH-DSA as a generic `SignatureAlg` in the `ProbComp` monad. -/
def slhdsaAlg [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    SignatureAlg ProbComp (List Byte) (PublicKey prims) (SecretKey prims) (Signature prims) where
  keygen := slhKeygen prims
  sign _pk sk msg := slhSign prims sk msg
  verify pk msg σ := pure (slhVerify prims pk msg σ)

/-- **Perfect completeness of SLH-DSA** (FIPS 205 §9 correctness): every honestly generated
signature verifies, with probability one. Proved with no `sorry` from the deterministic core
`slhVerifyInternal_slhSignInternal`. -/
theorem slhdsaAlg_perfectlyComplete [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    (slhdsaAlg prims).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  set mx : ProbComp Bool := do
    let (pk, sk) ← (slhdsaAlg prims).keygen
    let sig ← (slhdsaAlg prims).sign pk sk msg
    (slhdsaAlg prims).verify pk msg sig with hmx
  have huniq : ∀ y ∈ support mx, y = true := by
    intro y hy
    rw [hmx] at hy
    simp only [slhdsaAlg] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨⟨pk, sk⟩, hpksk, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨sig, hsig, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [slhKeygen] at hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨skSeed, -, hpksk⟩ := hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨skPrf, -, hpksk⟩ := hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨pkSeed, -, hpksk⟩ := hpksk
    simp only [support_pure, Set.mem_singleton_iff] at hpksk
    simp only [slhSign] at hsig
    rw [mem_support_bind_iff] at hsig
    obtain ⟨addrnd, -, hsig⟩ := hsig
    simp only [support_pure, Set.mem_singleton_iff] at hsig
    subst hsig
    have hpk : pk = (slhKeygenInternal prims skSeed skPrf pkSeed).1 := congrArg Prod.fst hpksk
    have hsk : sk = (slhKeygenInternal prims skSeed skPrf pkSeed).2 := congrArg Prod.snd hpksk
    subst hpk; subst hsk
    exact slhVerifyInternal_slhSignInternal prims msg skSeed skPrf pkSeed addrnd
  change Pr[= true | mx] = 1
  exact probOutput_eq_one_of_support_subset_singleton
    (NeverFail.probFailure_eq_zero (mx := mx)) huniq

end SLHDSA
