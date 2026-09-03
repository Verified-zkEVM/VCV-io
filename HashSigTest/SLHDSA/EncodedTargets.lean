/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.EncodedTargets

/-!
# SLH-DSA encoded target-ledger canaries

Executable checks that the concrete address encoders keep the reachable target ledgers
duplicate-free, and that no listed address reaches the SHA-2 zero fallback.  Both are run at the
values, not through the theorems: `Sha2Address.ofAdrs` is applied to every ledger entry and the
encoded key lists are compared for duplicates directly.

A separate group pins the negative direction.  Addresses outside the compressed SHA-2 domain
collapse onto the all-zero key, which is itself the genuine key of the all-zero WOTS-hash address,
so the checks confirm the ledger really does avoid that collapse rather than treating the fallback
as a sentinel.
-/

@[expose] public section

namespace SLHDSA.EncodedTargetsTest

open Security Concrete

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"encoded target-ledger check failed: {label}")

/-- Two layers of height two, two FORS trees of height two, `w = 16`, `len = 4`. -/
def twoLayerParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 2, k := 2, lgw := 4 }

def twoLayer : ValidatedParams := ⟨twoLayerParams, by decide⟩

def ledgers (vp : ValidatedParams) : List (String × List Adrs) :=
  [("FORS leaves", forsLeafAddresses vp),
   ("FORS internal nodes", forsTreeAddresses vp),
   ("FORS roots", forsRootAddresses vp),
   ("XMSS internal nodes", xmssNodeAddresses vp),
   ("WOTS+ steps", wotsStepAddresses vp),
   ("WOTS+ public keys", wotsPkAddresses vp)]

/-- Every ledger address passes the checked SHA-2 compression boundary, so none of them is encoded
through the zero fallback. -/
def checkSha2Domain (profile : String) (vp : ValidatedParams) : IO Unit := do
  for (label, addresses) in ledgers vp do
    ensure s!"{profile} {label}: every address is accepted by the checked SHA-2 boundary"
      (addresses.all fun a => (Sha2Address.ofAdrs a).toOption.isSome)
    ensure s!"{profile} {label}: no address compresses to the zero key"
      (addresses.all fun a => a = Adrs.zero || sha2AdrsKey a != zeroBytes 22)

/-- The two approved encoders at their concrete key widths.  Each is the primitive bundle's own
`encodeTargets`, pinned below. -/
def sha2Keys (addresses : List Adrs) : List (Bytes 22) := addresses.map sha2AdrsKey

def shakeKeys (addresses : List Adrs) : List (Bytes 32) := addresses.map Adrs.toVector

example (p : Params) (addresses : List Adrs) :
    encodeTargets (sha2Primitives p) addresses = sha2Keys addresses := rfl

example (p : Params) (addresses : List Adrs) :
    encodeTargets (shakePrimitives p) addresses = shakeKeys addresses := rfl

/-- Encoded tweaks stay distinct under both approved encoders. -/
def checkEncodedNodup (profile : String) (vp : ValidatedParams) : IO Unit := do
  for (label, addresses) in ledgers vp do
    ensure s!"{profile} {label}: SHA-2 encoded tweaks are distinct"
      (decide (sha2Keys addresses).Nodup)
    ensure s!"{profile} {label}: SHAKE encoded tweaks are distinct"
      (decide (shakeKeys addresses).Nodup)

/-- The compressed SHA-2 key really does lose information outside its domain: an address whose
tree index exceeds eight bytes is rejected by the checked boundary and aliases the zero key. -/
def checkFallbackAliasing : IO Unit := do
  let wide : Adrs := (Adrs.zero.setTypeAndClear .wotsHash).setTreeAddress (2 ^ 64)
  ensure "an over-wide tree index is rejected by the checked boundary"
    (Sha2Address.ofAdrs wide).toOption.isNone
  ensure "an over-wide tree index aliases the zero key"
    (sha2AdrsKey wide == zeroBytes 22)
  ensure "the all-zero WOTS-hash address has the same key"
    (sha2AdrsKey Adrs.zero == zeroBytes 22)
  ensure "the two distinct addresses are therefore not separated by the encoder"
    (wide != Adrs.zero && sha2AdrsKey wide == sha2AdrsKey Adrs.zero)

/-! ## Kernel-checked parameter bounds -/

example : Params.ApprovedAddressBounds twoLayerParams :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

def main : IO Unit := do
  checkSha2Domain "two-layer" twoLayer
  checkEncodedNodup "two-layer" twoLayer
  checkFallbackAliasing
  IO.println "SLH-DSA encoded target-ledger tests: PASS \
    (checked SHA-2 domain, SHA-2 and SHAKE encoded distinctness, fallback aliasing)"

end SLHDSA.EncodedTargetsTest

def main : IO Unit := SLHDSA.EncodedTargetsTest.main
