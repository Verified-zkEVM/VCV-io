/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.C13.Params
import HashSig.SLHDSA.C13.Primitives

/-!
# WOTS+C (C13)

The compact Winternitz one-time signature of the C-series (ePrint 2025/2203): the Winternitz
checksum chains are dropped, and a 32-bit counter is ground so the `l = 43` base-`w` message
digits sum to a fixed `targetSum = 208`. The digits are sliced LSB-first from
`H_wots(PK.seed, ADRS, node, counter)` (matching the `SPHINCs-C13Asm.sol` verifier):
`digitᵢ = (H_wots(…) ≫ (i·lgw)) mod w`.

Public-key recovery (`wotsPkFromSig`) reproduces public-key generation (`wotsPkGen`) on an
honest signature — the same hash-chain composition (`chain_compose`) that drives FIPS WOTS, with
the digits now coming from the counter-mixed hash. The fixed-sum gate `digitSumOk` is a
verifier-side check (honest signatures satisfy it by the grind); it is not needed for
pk-recovery correctness, but underpins unforgeability via the constant-sum specialization of
`SLHDSA.WotsChecksum`.

## References

- ePrint 2025/2203 (WOTS+C); the SPHINCs- repo verifier `src/SPHINCs-C13Asm.sol`
-/


namespace SLHDSA.C13

open SLHDSA (Adrs)

/-! ### Hash chain -/

/-- `chain(X, i, s)`: apply `F` `s` times from hash index `i` (as in FIPS WOTS). -/
def chain (prims : Primitives) (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y)
    (i : ℕ) : ℕ → prims.Y
  | 0 => x
  | s + 1 => prims.F pkSeed (adrs.setHashAddress (i + s)) (chain prims pkSeed adrs x i s)

/-- Hash-chain composition. -/
theorem chain_compose (prims : Primitives) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i a b : ℕ) :
    chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b
      = chain prims pkSeed adrs x i (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change prims.F pkSeed (adrs.setHashAddress (i + a + b))
          (chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b)
        = prims.F pkSeed (adrs.setHashAddress (i + (a + b)))
          (chain prims pkSeed adrs x i (a + b))
    rw [ih, Nat.add_assoc]

/-! ### WOTS+C digits (counter-mixed, LSB-first) -/

/-- The `i`-th base-`w` WOTS+C digit of `node` under `counter`: `(H_wots ≫ i·lgw) mod w`. -/
def digit (prims : Primitives) (pkSeed : prims.PkSeed) (adrs : Adrs) (node : prims.Y)
    (count i : ℕ) : ℕ :=
  (prims.Hwots pkSeed adrs node count >>> (i * params.lgw)) % params.w

theorem digit_lt (prims : Primitives) (pkSeed : prims.PkSeed) (adrs : Adrs) (node : prims.Y)
    (count i : ℕ) : digit prims pkSeed adrs node count i < params.w := by
  unfold digit; exact Nat.mod_lt _ (by decide)

/-- The WOTS+C digit sum over the `l` chains (the quantity the counter grinds to `targetSum`). -/
def digitSum (prims : Primitives) (pkSeed : prims.PkSeed) (adrs : Adrs) (node : prims.Y)
    (count : ℕ) : ℕ :=
  ((List.range wotsLen).map (digit prims pkSeed adrs node count)).sum

/-- Verifier-side fixed-sum gate: the `l` digits must sum to exactly `targetSum`. -/
def digitSumOk (prims : Primitives) (pkSeed : prims.PkSeed) (adrs : Adrs) (node : prims.Y)
    (count : ℕ) : Bool :=
  decide (digitSum prims pkSeed adrs node count = targetSum)

/-! ### WOTS+C addresses -/

/-- Address for the `F`-steps of chain `i` (type `WOTS_HASH`, key-pair preserved). -/
def wotsChainAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsHash).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Address for deriving the secret value of chain `i` (type `WOTS_PRF`). -/
def wotsSkAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsPrf).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Address for compressing the chain ends into the WOTS public key (type `WOTS_PK`). -/
def wotsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .wotsPk).setKeyPairAddress adrs.getKeyPairAddress

/-! ### Public-key generation, signing, and recovery -/

/-- A WOTS+C signature: the `l` chain values. -/
abbrev WotsSig (prims : Primitives) := Vector prims.Y wotsLen

/-- The `l` chain ends of the WOTS+C public key (chain each secret to the top `w-1`). -/
def wotsPkGenTops (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Vector prims.Y wotsLen :=
  Vector.ofFn fun i : Fin wotsLen =>
    chain prims pk (wotsChainAdrs adrs i.val) (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0
      (params.w - 1)

/-- WOTS+C public-key generation. -/
def wotsPkGen (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  prims.Tl pk (wotsPkAdrs adrs) (wotsPkGenTops prims sk pk adrs).toList

/-- WOTS+C signing under a (grinding-found) `counter`: chain each secret to its message digit. -/
def wotsSign (prims : Primitives) (node : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (count : ℕ) : WotsSig prims :=
  Vector.ofFn fun i : Fin wotsLen =>
    chain prims pk (wotsChainAdrs adrs i.val) (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0
      (digit prims pk adrs node count i.val)

/-- The `l` chain ends recovered from a WOTS+C signature. -/
def wotsPkFromSigTops (prims : Primitives) (sig : WotsSig prims) (node : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) (count : ℕ) : Vector prims.Y wotsLen :=
  Vector.ofFn fun i : Fin wotsLen =>
    chain prims pk (wotsChainAdrs adrs i.val) sig[i.val] (digit prims pk adrs node count i.val)
      (params.w - 1 - digit prims pk adrs node count i.val)

/-- WOTS+C public-key recovery from a signature. -/
def wotsPkFromSig (prims : Primitives) (sig : WotsSig prims) (node : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) (count : ℕ) : prims.Y :=
  prims.Tl pk (wotsPkAdrs adrs) (wotsPkFromSigTops prims sig node pk adrs count).toList

/-! ### Correctness -/

theorem wotsPkFromSigTops_wotsSign (prims : Primitives) (node : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (count : ℕ) :
    wotsPkFromSigTops prims (wotsSign prims node sk pk adrs count) node pk adrs count
      = wotsPkGenTops prims sk pk adrs := by
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops, wotsSign, wotsPkGenTops, Vector.getElem_ofFn]
  have hc := chain_compose prims pk (wotsChainAdrs adrs i)
    (prims.PRF pk sk (wotsSkAdrs adrs i)) 0 (digit prims pk adrs node count i)
    (params.w - 1 - digit prims pk adrs node count i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (digit_lt prims pk adrs node count i))]

/-- **WOTS+C correctness**: recovering the public key from an honest signature reproduces
`wotsPkGen` (for any `counter`; the digit-sum gate is a separate verifier check). -/
theorem wotsPkFromSig_wotsSign (prims : Primitives) (node : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (count : ℕ) :
    wotsPkFromSig prims (wotsSign prims node sk pk adrs count) node pk adrs count
      = wotsPkGen prims sk pk adrs := by
  unfold wotsPkFromSig wotsPkGen
  rw [wotsPkFromSigTops_wotsSign]

end SLHDSA.C13
