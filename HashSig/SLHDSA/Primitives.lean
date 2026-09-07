/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Address

/-!
# SLH-DSA Primitive Interfaces

The abstract interfaces for the six SLH-DSA hash/PRF functions (FIPS 205 §4.1), keeping the
hash family opaque while the WOTS+/XMSS/FORS/hypertree layers are defined generically over it.
A concrete instantiation (SHA-2 / SHAKE / keccak) supplies the fields later in a `Concrete`
layer without touching the proof-level development.

`CorePrimitives` contains the carrier types, address encoding, secret-key operations, and node
encoding needed to state the scheme independently of any implementation of the public hash
collection. `Primitives` extends that context with deterministic implementations of `Thash` and
`Hmsg`; the explicit-oracle layer packages those two fields as a `QueryImpl`.

The carrier types are abstract fields of the bundle, mirroring how `MLDSA.Primitives` carries
abstract `High`/`Hint` types:

| field | FIPS 205 | role |
|---|---|---|
| `Thash`  | `T_ℓ(PK.seed, ADRS, Mₗ)`         | shared tweakable-hash collection |
| `PRF`    | `PRF(PK.seed, SK.seed, ADRS)`    | WOTS+/FORS secret values |
| `PRFmsg` | `PRF_msg(SK.prf, opt_rand, M)`   | message randomizer `R` |
| `Hmsg`   | `H_msg(R, PK.seed, PK.root, M)`  | message digest (`m` bytes) |

## Byte coherence and correctness vs. security

The operational bundle carries no cryptographic assumption. `Primitives.ByteLaws` is a separate,
optional structural law bundle asserting that the exposed `n`-byte representation distinguishes
nodes. Keeping it separate avoids burdening generic tree correctness with a property needed only
when byte-level digit extraction is related back to the abstract node carrier.

Unlike `MLDSA.Primitives`, this bundle carries no algebraic hash laws: SLH-DSA correctness
(`verify ∘ sign = accept`) is a *deterministic hash-tree consistency identity* that holds for
**any** choice of the opaque hash fields — it reduces to the fact that `wotsPkFromSig`/
`computeRoot` re-fold the *same* `F`/`H`/`Tl` at the *same* addresses the honest signer used,
provable by structural induction with no hash hypotheses. The cryptographic assumptions needed
for unforgeability concern pseudorandomness of `PRF`/`PRFmsg`, multi-target collision and
decisional second-preimage resistance of the tweakable hashes, and interleaved target subset
resilience of `Hmsg`. `HashSig.SLHDSA.Security` packages the primitive families into generic
VCVio interfaces.

## References

- NIST FIPS 205, §4.1 (the six functions), §11 (their instantiations)
-/

@[expose] public section


namespace SLHDSA

/-- The implementation-independent SLH-DSA context: carrier types, canonical address encoding,
secret-key PRFs, and the byte encoding of nodes. It deliberately contains no implementation of
the public `Thash` / `Hmsg` collection, so oracle-parametric scheme programs can depend on this
context without gaining access to a concrete public hash function. -/
structure CorePrimitives (p : Params) where
  /-- Public seed type (`PK.seed`). -/
  PkSeed : Type
  /-- Secret seed type (`SK.seed`), expanded by `PRF` into WOTS+/FORS secret values. -/
  SkSeed : Type
  /-- Message-PRF key type (`SK.prf`), keyed into `PRFmsg`. -/
  SkPrf : Type
  /-- Node / hash-output type (`n`-byte values: seeds, chain values, tree nodes, roots). -/
  Y : Type
  /-- Fixed-width canonical address key used by this instantiation. -/
  AdrsKey : Type
  /-- Canonicalize a structural address into the exact fixed-width key hashed by the
  instantiation.  SHA-2 uses `Bytes 22`; SHAKE uses `Bytes 32`. -/
  adrsToKey : Adrs → AdrsKey
  /-- `PRF(PK.seed, SK.seed, ADRS)`: derive a WOTS+/FORS secret value. -/
  PRF : PkSeed → SkSeed → Adrs → Y
  /-- `PRF_msg(SK.prf, opt_rand, M)`: derive the message randomizer `R`. -/
  PRFmsg : SkPrf → Y → List Byte → Y
  /-- Expose the `n`-byte encoding of a node, so WOTS+/FORS can extract base-`w`/`a` digits
  from a node via `base2b` (the only byte-level bridge needed by the abstract layer). -/
  yToBytes : Y → Bytes p.n

/-- A deterministic implementation of all SLH-DSA primitives. `F`, `H = T₂`, and `T_ℓ` are
arity-specific views of the one `Thash` collection, keyed by the exact address encoding carried
by `CorePrimitives`. The public operations are separated from the inherited context so the same
scheme syntax can instead be interpreted by an explicit oracle. -/
structure Primitives (p : Params) extends CorePrimitives p where
  /-- The single variable-arity tweakable-hash collection underlying `F`, `H = T₂`, and `T_ℓ`.
  The ordered list length and contents are part of its input. -/
  Thash : PkSeed → AdrsKey → List Y → Y
  /-- `H_msg(R, PK.seed, PK.root, M)`: the `m`-byte message digest. -/
  Hmsg : Y → PkSeed → Y → List Byte → Bytes p.m

namespace Primitives

variable {p : Params}

/-- Forget the deterministic public hash implementation while retaining the scheme context. -/
@[reducible] def core (prims : Primitives p) : CorePrimitives p := prims.toCorePrimitives

end Primitives

/-- A deterministic primitive bundle may be used wherever only the implementation-independent
scheme context is required. -/
instance {p : Params} : Coe (Primitives p) (CorePrimitives p) := ⟨Primitives.core⟩

namespace Primitives

variable {p : Params}

/-- `F(PK.seed, ADRS, M₁) = T₁(PK.seed, ADRS, [M₁])`. -/
@[reducible] def F (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) : prims.Y :=
  prims.Thash pkSeed (prims.adrsToKey adrs) [x]

/-- `H(PK.seed, ADRS, Mₗ ‖ Mᵣ) = T₂(PK.seed, ADRS, [Mₗ, Mᵣ])`. -/
@[reducible] def H (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (left right : prims.Y) : prims.Y :=
  prims.Thash pkSeed (prims.adrsToKey adrs) [left, right]

/-- `T_ℓ(PK.seed, ADRS, M)` for an ordered variable-length node list. -/
@[reducible] def Tl (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (xs : List prims.Y) : prims.Y :=
  prims.Thash pkSeed (prims.adrsToKey adrs) xs

end Primitives

namespace CorePrimitives

/-- The byte bridge is coherent when equal encodings imply equal abstract nodes. This is the only
representation law required by downstream digit-extraction arguments; it is not a collision-
resistance or pseudorandomness assumption. -/
structure ByteLaws {p : Params} (primitives : CorePrimitives p) : Prop where
  yToBytes_injective : Function.Injective primitives.yToBytes

/-- Under byte coherence, node equality is characterized by equality of the fixed-width byte
encodings. -/
theorem ByteLaws.yToBytes_eq_iff {p : Params} {primitives : CorePrimitives p}
    (laws : primitives.ByteLaws) (x y : primitives.Y) :
    primitives.yToBytes x = primitives.yToBytes y ↔ x = y :=
  ⟨fun h => laws.yToBytes_injective h, congrArg primitives.yToBytes⟩

end CorePrimitives

end SLHDSA
