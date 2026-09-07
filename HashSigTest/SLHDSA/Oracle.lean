/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Oracle
public import HashSig.SLHDSA.Concrete.Instance

/-!
# Producer canaries for the SLH-DSA public-hash collection

These examples cover distinct observable contracts: query domain separation, the shared
`F`/`H`/`T_ℓ` collection, canonical address encoding, deterministic interpretation, and
lazy-cache hit/miss behavior.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.PublicHashTest

abbrev Q := PublicHashQuery Nat Nat Nat

/-- Every field of a tweakable-hash query contributes to its cache identity. -/
example :
    (PublicHashQuery.thash 0 0 [7] : Q) ≠ PublicHashQuery.thash 1 0 [7] ∧
    (PublicHashQuery.thash 0 0 [7] : Q) ≠ PublicHashQuery.thash 0 1 [7] ∧
    (PublicHashQuery.thash 0 0 [3, 5] : Q) ≠ PublicHashQuery.thash 0 0 [5, 3] ∧
    (PublicHashQuery.thash 0 0 [3] : Q) ≠ PublicHashQuery.thash 0 0 [3, 0] := by
  decide

/-- `H_msg` is a separate domain, and all of its inputs contribute to query identity. -/
example :
    (PublicHashQuery.thash 0 0 [7] : Q) ≠ PublicHashQuery.hmsg 7 0 9 [] ∧
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 8 0 9 [] ∧
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 7 1 9 [] ∧
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 7 0 10 [] ∧
    (PublicHashQuery.hmsg 7 0 9 [] : Q) ≠ PublicHashQuery.hmsg 7 0 9 [0] := by
  decide

section Generic

variable {p : Params} (core : CorePrimitives p)

/-- `F` is definitionally the singleton-input member of the same collection as `T_ℓ`. -/
example (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y) :
    (PublicHash.f core pkSeed adrs x : OracleComp (publicHashSpec core) core.Y) =
      PublicHash.tl core pkSeed adrs [x] := rfl

/-- `H` is definitionally `T₂`, including the same cache identity. -/
example (pkSeed : core.PkSeed) (adrs : Adrs) (left right : core.Y) :
    (PublicHash.h core pkSeed adrs left right : OracleComp (publicHashSpec core) core.Y) =
      PublicHash.tl core pkSeed adrs [left, right] := rfl

/-- Addresses that serialize identically issue exactly the same oracle query. -/
example (pkSeed : core.PkSeed) (a b : Adrs) (x : core.Y)
    (h : core.adrsToKey a = core.adrsToKey b) :
    (PublicHash.f core pkSeed a x : OracleComp (publicHashSpec core) core.Y) =
      PublicHash.f core pkSeed b x := by
  unfold PublicHash.f
  rw [h]

variable [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes p.m)]

local instance publicHashRangeSampleable :
    ∀ q : PublicHashQuery core.PkSeed core.AdrsKey core.Y,
      SampleableType ((publicHashSpec core).Range q) := fun q => by
  cases q <;> infer_instance

/-- A populated cell is a cache hit: it returns the stored value without changing state. -/
example (q : PublicHashQuery core.PkSeed core.AdrsKey core.Y)
    (u : (publicHashSpec core).Range q) :
    (PublicHash.randomOracle core q).run
        ((∅ : PublicHash.Cache core).cacheQuery q u) =
      pure (u, (∅ : PublicHash.Cache core).cacheQuery q u) := by
  rw [randomOracle.run_eq, QueryCache.cacheQuery_self]

/-- An empty cell is a cache miss: it samples once and stores the sampled value. -/
example (q : PublicHashQuery core.PkSeed core.AdrsKey core.Y) :
    (PublicHash.randomOracle core q).run (∅ : PublicHash.Cache core) =
      ($ᵗ (publicHashSpec core).Range q) >>= fun u =>
        pure (u, (∅ : PublicHash.Cache core).cacheQuery q u) := by
  rw [randomOracle.run_eq, QueryCache.empty_apply]

end Generic

section Deterministic

variable {p : Params} (prims : Primitives p)

/-- The deterministic handler recovers the bundle's common tweakable hash. -/
example (pkSeed : prims.PkSeed) (adrs : Adrs) (left right : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (PublicHash.h prims.core pkSeed adrs left right :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      prims.H pkSeed adrs left right := by
  simp

end Deterministic

/-! The SHA-2 instance keys by the exact 22-byte `ADRSc`. -/

open Concrete

example : shaPrimitives.AdrsKey = Bytes 22 := rfl

example (adrs : Adrs) : (shaPrimitives.adrsToKey adrs).toList = adrs.compressSha2 := by
  change (shaAdrsKey adrs).toList = adrs.compressSha2
  exact shaAdrsKey_toList adrs

/-- SHA-2 compression intentionally truncates the layer to 8 bits and the tree to 64 bits. -/
example :
    shaPrimitives.adrsToKey Adrs.zero =
      shaPrimitives.adrsToKey (Adrs.zero.setLayerAddress 256) ∧
    shaPrimitives.adrsToKey Adrs.zero =
      shaPrimitives.adrsToKey (Adrs.zero.setTreeAddress (2 ^ 64)) := by
  constructor
  · change shaAdrsKey Adrs.zero = shaAdrsKey (Adrs.zero.setLayerAddress 256)
    apply Vector.toArray_inj.mp
    simpa [shaAdrsKey] using
      (show Adrs.zero.compressSha2 = (Adrs.zero.setLayerAddress 256).compressSha2 by
        norm_num [Adrs.compressSha2, Adrs.toBytesBE, toByte, Adrs.zero, Adrs.setLayerAddress])
  · change shaAdrsKey Adrs.zero = shaAdrsKey (Adrs.zero.setTreeAddress (2 ^ 64))
    apply Vector.toArray_inj.mp
    simpa [shaAdrsKey] using
      (show Adrs.zero.compressSha2 =
        (Adrs.zero.setTreeAddress (2 ^ 64)).compressSha2 by
          norm_num [Adrs.compressSha2, Adrs.toBytesBE, toByte, Adrs.zero,
            Adrs.setTreeAddress]
          decide)

/-- Every retained SHA-2 address field is observable in the compressed key. -/
example :
    Adrs.zero.compressSha2 ≠ (Adrs.zero.setLayerAddress 1).compressSha2 ∧
    Adrs.zero.compressSha2 ≠ (Adrs.zero.setTreeAddress 1).compressSha2 ∧
    Adrs.zero.compressSha2 ≠ (Adrs.zero.setTypeAndClear .wotsPk).compressSha2 ∧
    Adrs.zero.compressSha2 ≠ (Adrs.zero.setKeyPairAddress 1).compressSha2 ∧
    Adrs.zero.compressSha2 ≠ (Adrs.zero.setChainAddress 1).compressSha2 ∧
    Adrs.zero.compressSha2 ≠ (Adrs.zero.setHashAddress 1).compressSha2 := by
  constructor
  · intro h
    exact (by decide : Adrs.zero ≠ Adrs.zero.setLayerAddress 1)
      (Adrs.compressSha2_injective_of_fits
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h)
  constructor
  · intro h
    exact (by decide : Adrs.zero ≠ Adrs.zero.setTreeAddress 1)
      (Adrs.compressSha2_injective_of_fits
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h)
  constructor
  · intro h
    exact (by decide : Adrs.zero ≠ Adrs.zero.setTypeAndClear .wotsPk)
      (Adrs.compressSha2_injective_of_fits
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h)
  constructor
  · intro h
    exact (by decide : Adrs.zero ≠ Adrs.zero.setKeyPairAddress 1)
      (Adrs.compressSha2_injective_of_fits
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h)
  constructor
  · intro h
    exact (by decide : Adrs.zero ≠ Adrs.zero.setChainAddress 1)
      (Adrs.compressSha2_injective_of_fits
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h)
  · intro h
    exact (by decide : Adrs.zero ≠ Adrs.zero.setHashAddress 1)
      (Adrs.compressSha2_injective_of_fits
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h)

end SLHDSA.PublicHashTest
