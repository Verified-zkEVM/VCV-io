/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Scheme
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.PRF

/-!
# SLH-DSA Cryptographic Primitive Families

This module packages the hash and pseudorandom-function primitives used by `slhdsaAlg` into the
generic `TweakableHash` and `PRFScheme` interfaces:

- `Primitives.fHash` and `Primitives.hHash` expose `F` and `H` as tweakable hash families with
  the instantiation's canonical encoded `AdrsKey` as the tweak;
- `Primitives.thashCollection` packages every fixed input arity of `Thash` under one public seed
  and encoded-address space;
- `Primitives.msgPrfScheme` exposes the message randomizer `PRF_msg`; and
- `Primitives.skPrfScheme` exposes the secret-value derivation function `PRF` at a public seed.

These packages identify the primitive families to which an SLH-DSA security reduction applies.
An aggregate EUF-CMA theorem additionally needs the seed-aware collection games under
`HardnessAssumptions.TweakableHash`, SM-DT-DSPR and SM-DT-OpenPRE/UD variants, an `H_msg`
interleaved-target-subset-resilience game, explicit reductions from the forger, and checked query
bounds. Primitive packaging alone does not supply those ingredients.

## References

- Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, Schwabe, "The SPHINCS+ Signature Framework"
- Hülsing, Rijneveld, and Song, "Mitigating Multi-Target Attacks in Hash-Based Signatures"
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
- NIST FIPS 205, §10 (security)
-/

@[expose] public section


open OracleComp OracleSpec ENNReal

namespace SLHDSA

variable {p : Params} (prims : Primitives p)

/-! ### The SLH-DSA hashes as tweakable hash families / PRFs -/

/-- The chain-step / FORS-leaf hash `F` as a tweakable hash family.  Its tweak is the exact
encoded address hashed by the concrete instantiation. -/
def Primitives.fHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed prims.AdrsKey prims.Y prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrsKey x => prims.Thash pkSeed adrsKey [x]

/-- The Merkle / FORS-tree node hash `H` as a tweakable hash family over encoded addresses and
ordered sibling pairs. -/
def Primitives.hHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed prims.AdrsKey (prims.Y × prims.Y) prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrsKey m => prims.Thash pkSeed adrsKey [m.1, m.2]

/-- The fixed-arity members of SLH-DSA's public `Thash` collection.  Member `arity` accepts
exactly `arity` ordered nodes, while all members share the sampled public seed, canonical encoded
address space, and output type. -/
def Primitives.thashCollection :
    TweakableHashCollection ℕ prims.PkSeed prims.AdrsKey prims.Y where
  Msg arity := Vector prims.Y arity
  eval := fun _ pkSeed adrsKey xs => prims.Thash pkSeed adrsKey xs.toList

/-- The fixed-arity member of SLH-DSA's public `Thash` collection. -/
def Primitives.thashMember [SampleableType prims.PkSeed] (arity : ℕ) :
    TweakableHash prims.PkSeed prims.AdrsKey (Vector prims.Y arity) prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrsKey xs => prims.Thash pkSeed adrsKey xs.toList

/-- Evaluating the collection at `arity` is definitionally the same operation as evaluating the
corresponding fixed-arity member. -/
@[simp] theorem Primitives.thashCollection_eval [SampleableType prims.PkSeed] (arity : ℕ) :
    prims.thashCollection.eval arity = (prims.thashMember arity).eval := rfl

/-- The SM-DT-TCR problem for the `arity`-input member of `Thash`, with the whole `Thash`
collection available during target selection. -/
def Primitives.thashTcrProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ) :
    TweakableHash.SM_DT_TCR_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  thColl := prims.thashCollection
  numTargets := numTargets

/-- The unrestricted-subspace SM-DT-PRE problem for the `arity`-input member of `Thash`, with the
whole `Thash` collection available during target selection. -/
def Primitives.thashPreProblem [SampleableType prims.PkSeed] (arity numTargets : ℕ) :
    TweakableHash.SM_DT_PRE_Problem ℕ prims.PkSeed prims.AdrsKey
      (Vector prims.Y arity) (Vector prims.Y arity) prims.Y where
  th := prims.thashMember arity
  emb := id
  emb_injective := Function.injective_id
  thColl := prims.thashCollection
  numTargets := numTargets

/-- The message randomizer `PRF_msg` as a `PRFScheme` keyed by `SK.prf`; `eval` is
`prims.PRFmsg`. -/
def msgPrfScheme [SampleableType prims.SkPrf] :
    PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y where
  keygen := $ᵗ prims.SkPrf
  eval := fun skPrf rm => prims.PRFmsg skPrf rm.1 rm.2

/-- The secret-value `PRF` at public seed `pkSeed` as a `PRFScheme` keyed by `SK.seed`; `eval` is
`prims.PRF pkSeed`. -/
def skPrfScheme [SampleableType prims.SkSeed] (pkSeed : prims.PkSeed) :
    PRFScheme prims.SkSeed Adrs prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun skSeed adrs => prims.PRF pkSeed skSeed adrs

end SLHDSA
