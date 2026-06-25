/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Address

/-!
# C13 primitive interfaces

The abstract hash bundle for the C13 variant. The tree hashes `F`/`H`/`T_ℓ` and the secret PRF
have the same shape as the FIPS family (`PkSeed → ADRS → … → Y`), but C13's message-dependent
hashes are different and so are modeled separately:

- `Hmsg` returns the `keccak256` message digest as a **256-bit integer** (`ℕ`); C13 then slices
  it with shifts/masks (LSB-first), matching the on-chain `SPHINCs-C13Asm.sol` verifier — note
  this is C13's own convention, not the FIPS 205 MSB-first parsing of the SHA-2 variant.
- `Hwots` returns the **WOTS+C message hash** `keccak256(PK.seed ‖ ADRS ‖ node ‖ counter)` as a
  256-bit integer, from which the `l` base-`w` WOTS+C digits are sliced; the counter is ground so
  the digits sum to `targetSum`.

As with the FIPS abstract layer, the bundle carries plain functions (no algebraic laws): C13
correctness is a deterministic hash-tree identity; the cryptographic assumptions live in the
security layer.
-/


namespace SLHDSA.C13

open SLHDSA

/-- The C13 tweakable-hash / PRF bundle (keccak256 instantiation supplied in `C13.Concrete`). -/
structure Primitives where
  /-- Public seed type. -/
  PkSeed : Type
  /-- Secret seed type. -/
  SkSeed : Type
  /-- Message-PRF key type. -/
  SkPrf : Type
  /-- Node / hash-output type (`n`-byte values). -/
  Y : Type
  /-- `F`: one-block tweakable hash (WOTS+C chain step, FORS leaf). -/
  F : PkSeed → Adrs → Y → Y
  /-- `H`: two-block tweakable hash (Merkle / FORS-tree node). -/
  H : PkSeed → Adrs → Y → Y → Y
  /-- `T_ℓ`: compress a list of nodes (WOTS-pk, FORS roots). -/
  Tl : PkSeed → Adrs → List Y → Y
  /-- `PRF`: derive a WOTS+C / FORS secret value. -/
  PRF : PkSeed → SkSeed → Adrs → Y
  /-- `PRF_msg`: derive the message randomizer `R`. -/
  PRFmsg : SkPrf → Y → List Byte → Y
  /-- `H_msg(R, PK.seed, PK.root, M)` as the 256-bit keccak digest (LSB-first sliced by C13). -/
  Hmsg : Y → PkSeed → Y → List Byte → ℕ
  /-- `H_wots(PK.seed, ADRS, node, counter)` as the 256-bit keccak digest feeding the WOTS+C
  base-`w` digits. -/
  Hwots : PkSeed → Adrs → Y → ℕ → ℕ

end SLHDSA.C13
