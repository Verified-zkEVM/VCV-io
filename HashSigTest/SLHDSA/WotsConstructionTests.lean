/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module

public import HashSig.SLHDSA.Concrete.Wots

/-!
# Concrete WOTS+ Construction Tests

Executable construction-level regression coverage for every approved SHA2 and SHAKE profile.
Fixed-width deterministic inputs exercise `wotsSign`, `wotsPkFromSig`, and `wotsPkGen`; this is
not presented as an authoritative WOTS known-answer vector.  The SHA2 profiles additionally check
every WOTS secret, hash-step, and public-key address used by these executions through the rejecting
`Sha2Address.ofAdrs` boundary before comparing results, so the total primitive bundle's zero
fallback cannot mask the equality.
-/

@[expose] public section


namespace SLHDSA.WotsConstructionTests

open Concrete

def fixedBytes (n salt : ℕ) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (salt + 17 * i.val)

def baseAdrs : Adrs :=
  ((Adrs.zero.setLayerAddress 1).setTreeAddress 2).setKeyPairAddress 3

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"WOTS+ construction check failed: {label}")

/-- Explicitly check the complete SHA2 WOTS address domain exercised by signing, recovery, and
public-key generation.  Signing and recovery partition the same `0 .. w - 2` hash-step range. -/
def checkSha2WotsAddresses (set : FipsParameterSet) : IO Unit := do
  let p := set.params
  ensure s!"{set.name}: base SHA2 address" (Sha2Address.ofAdrs baseAdrs).isOk
  for i in List.range p.len do
    ensure s!"{set.name}: WOTS PRF address {i}"
      (Sha2Address.ofAdrs (wotsSkAdrs baseAdrs i)).isOk
    for j in List.range (p.w - 1) do
      ensure s!"{set.name}: WOTS chain/hash address {i}/{j}"
        (Sha2Address.ofAdrs ((wotsChainAdrs baseAdrs i).setHashAddress j)).isOk
  ensure s!"{set.name}: WOTS public-key address"
    (Sha2Address.ofAdrs (wotsPkAdrs baseAdrs)).isOk

def exerciseBundle {p : Params} (name : String) (prims : Primitives p)
    (skSeed : prims.SkSeed) (pkSeed : prims.PkSeed) (msg : prims.Y) : IO Unit := do
  let signature := wotsSign prims msg skSeed pkSeed baseAdrs
  let recovered := wotsPkFromSig prims signature msg pkSeed baseAdrs
  let generated := wotsPkGen prims skSeed pkSeed baseAdrs
  ensure s!"{name}: wotsSign -> wotsPkFromSig = wotsPkGen"
    (prims.core.yToBytes recovered == prims.core.yToBytes generated)

/-- Exercise the exact `approvedPrimitives` bundle for one named profile.  Splitting on the name
makes its fixed byte width definitionally visible without adding casts to the construction code. -/
def exerciseProfile : FipsParameterSet → IO Unit
  | .SLHDSA_SHA2_128s => do
      checkSha2WotsAddresses .SLHDSA_SHA2_128s
      exerciseBundle FipsParameterSet.SLHDSA_SHA2_128s.name
        (approvedPrimitives .SLHDSA_SHA2_128s)
        (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3)
  | .SLHDSA_SHA2_128f => do
      checkSha2WotsAddresses .SLHDSA_SHA2_128f
      exerciseBundle FipsParameterSet.SLHDSA_SHA2_128f.name
        (approvedPrimitives .SLHDSA_SHA2_128f)
        (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3)
  | .SLHDSA_SHA2_192s => do
      checkSha2WotsAddresses .SLHDSA_SHA2_192s
      exerciseBundle FipsParameterSet.SLHDSA_SHA2_192s.name
        (approvedPrimitives .SLHDSA_SHA2_192s)
        (fixedBytes 24 1) (fixedBytes 24 2) (fixedBytes 24 3)
  | .SLHDSA_SHA2_192f => do
      checkSha2WotsAddresses .SLHDSA_SHA2_192f
      exerciseBundle FipsParameterSet.SLHDSA_SHA2_192f.name
        (approvedPrimitives .SLHDSA_SHA2_192f)
        (fixedBytes 24 1) (fixedBytes 24 2) (fixedBytes 24 3)
  | .SLHDSA_SHA2_256s => do
      checkSha2WotsAddresses .SLHDSA_SHA2_256s
      exerciseBundle FipsParameterSet.SLHDSA_SHA2_256s.name
        (approvedPrimitives .SLHDSA_SHA2_256s)
        (fixedBytes 32 1) (fixedBytes 32 2) (fixedBytes 32 3)
  | .SLHDSA_SHA2_256f => do
      checkSha2WotsAddresses .SLHDSA_SHA2_256f
      exerciseBundle FipsParameterSet.SLHDSA_SHA2_256f.name
        (approvedPrimitives .SLHDSA_SHA2_256f)
        (fixedBytes 32 1) (fixedBytes 32 2) (fixedBytes 32 3)
  | .SLHDSA_SHAKE_128s =>
      exerciseBundle FipsParameterSet.SLHDSA_SHAKE_128s.name
        (approvedPrimitives .SLHDSA_SHAKE_128s)
        (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3)
  | .SLHDSA_SHAKE_128f =>
      exerciseBundle FipsParameterSet.SLHDSA_SHAKE_128f.name
        (approvedPrimitives .SLHDSA_SHAKE_128f)
        (fixedBytes 16 1) (fixedBytes 16 2) (fixedBytes 16 3)
  | .SLHDSA_SHAKE_192s =>
      exerciseBundle FipsParameterSet.SLHDSA_SHAKE_192s.name
        (approvedPrimitives .SLHDSA_SHAKE_192s)
        (fixedBytes 24 1) (fixedBytes 24 2) (fixedBytes 24 3)
  | .SLHDSA_SHAKE_192f =>
      exerciseBundle FipsParameterSet.SLHDSA_SHAKE_192f.name
        (approvedPrimitives .SLHDSA_SHAKE_192f)
        (fixedBytes 24 1) (fixedBytes 24 2) (fixedBytes 24 3)
  | .SLHDSA_SHAKE_256s =>
      exerciseBundle FipsParameterSet.SLHDSA_SHAKE_256s.name
        (approvedPrimitives .SLHDSA_SHAKE_256s)
        (fixedBytes 32 1) (fixedBytes 32 2) (fixedBytes 32 3)
  | .SLHDSA_SHAKE_256f =>
      exerciseBundle FipsParameterSet.SLHDSA_SHAKE_256f.name
        (approvedPrimitives .SLHDSA_SHAKE_256f)
        (fixedBytes 32 1) (fixedBytes 32 2) (fixedBytes 32 3)

def main : IO Unit := do
  for set in FipsParameterSet.all do
    exerciseProfile set
  IO.println "SLH-DSA S05 WOTS+ construction tests: PASS \
    (SHA2/SHAKE; 12 profiles; checked SHA2 addresses)"

end SLHDSA.WotsConstructionTests

def main : IO Unit := SLHDSA.WotsConstructionTests.main
