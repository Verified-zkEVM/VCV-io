/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.C13.Params
import HashSig.SLHDSA.C13.Primitives
import HashSig.SLHDSA.Xmss

/-!
# FORS+C (C13)

The compact few-time forest of the C-series: `k = 7` FORS trees, but the **last** tree's leaf
index is ground to `0`, so its authentication path is omitted and only its revealed leaf-0
secret is hashed (a degenerate height-0 contribution); the other `k − 1` trees climb their auth
paths normally. The `k` roots are compressed by `T_k`. FORS indices are sliced LSB-first from the
`keccak256` message digest (read as a 256-bit integer), matching `SPHINCs-C13Asm.sol`.

Reuses the generic Merkle theory `SLHDSA.Merkle`. `forsPkFromSig` reproduces `forsPkGen` on an
honest signature, given the forced-zero condition `forsIdx digest (k-1) = 0` (which the message
randomizer is ground to satisfy).

## References

- ePrint 2025/2203 (FORS+C); the SPHINCs- repo verifier `src/SPHINCs-C13Asm.sol`
-/


namespace SLHDSA.C13

open SLHDSA (Adrs)
open SLHDSA.Merkle

/-! ### Addresses, secret values, leaves, tree roots -/

/-- FORS secret-value address at global leaf index `t` (type `FORS_PRF`). -/
def forsSkAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .forsPrf).setKeyPairAddress adrs.getKeyPairAddress).setTreeIndex t

/-- FORS secret value at global leaf index `t`. -/
def forsSkGen (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  prims.PRF pk sk (forsSkAdrs adrs t)

/-- FORS-tree node address at `(height z, global index t)` (type `FORS_TREE`). -/
def forsNodeAdrs (adrs : Adrs) (z t : ℕ) : Adrs :=
  let base := (adrs.setTypeAndClear .forsTree).setKeyPairAddress adrs.getKeyPairAddress
  (base.setTreeHeight z).setTreeIndex t

/-- FORS leaf value at global index `t`: `F` of the secret value. -/
def forsLeaf (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  prims.F pk (forsNodeAdrs adrs 0 t) (forsSkGen prims sk pk adrs t)

/-- FORS internal-node hash at `(height z, global index t)`. -/
def forsNodeHash (prims : Primitives) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  prims.H pk (forsNodeAdrs adrs z t) l r

/-- Root of FORS tree `i` (height-`a` node at index `i`). -/
def forsRoot (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (i : ℕ) : prims.Y :=
  merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) params.a i

/-- FORS-roots compression address (type `FORS_ROOTS`). -/
def forsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .forsRoots).setKeyPairAddress adrs.getKeyPairAddress

/-! ### FORS+C indices and the forced-zero gate -/

/-- The selected leaf index in tree `i`: the `i`-th `a`-bit LSB-first slice of the digest. -/
def forsIdx (digest i : ℕ) : ℕ := (digest >>> (i * params.a)) % 2 ^ params.a

theorem forsIdx_lt (digest i : ℕ) : forsIdx digest i < 2 ^ params.a :=
  Nat.mod_lt _ (by positivity)

/-- Verifier-side forced-zero gate: the last tree's index must be `0`. -/
def forcedZeroOk (digest : ℕ) : Bool := decide (forsIdx digest (params.k - 1) = 0)

/-! ### Public key, signing, recovery -/

/-- The FORS+C public key: `T_k` over `k − 1` full tree roots plus the degenerate leaf-0 hash of
the forced-zero last tree (its auth path is omitted). -/
def forsPkGen (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  prims.Tl pk (forsPkAdrs adrs) ((List.finRange params.k).map fun i =>
    if i.val < params.k - 1 then forsRoot prims sk pk adrs i.val
    else forsLeaf prims sk pk adrs ((params.k - 1) * 2 ^ params.a))

/-- A FORS+C signature: per tree, the revealed leaf secret and (for the first `k − 1` trees) its
auth path; the last tree carries no auth path (`[]`). -/
abbrev ForsSig (prims : Primitives) := Vector (prims.Y × List prims.Y) params.k

/-- FORS+C signing under a digest whose last index is forced to `0`. -/
def forsCSign (prims : Primitives) (digest : ℕ) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : ForsSig prims :=
  Vector.ofFn fun i : Fin params.k =>
    let t := i.val * 2 ^ params.a + forsIdx digest i.val
    (forsSkGen prims sk pk adrs t,
      if i.val < params.k - 1 then
        authPath (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) 0 t params.a
      else [])

/-- FORS+C public-key recovery: reconstruct each tree's root (the last from its revealed leaf
secret alone), then compress with `T_k`. -/
def forsCPkFromSig (prims : Primitives) (sig : ForsSig prims) (digest : ℕ)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  prims.Tl pk (forsPkAdrs adrs) ((List.finRange params.k).map fun i =>
    let t := i.val * 2 ^ params.a + forsIdx digest i.val
    let leaf := prims.F pk (forsNodeAdrs adrs 0 t) (sig[i.val]).1
    if i.val < params.k - 1 then climb (forsNodeHash prims pk adrs) 0 t leaf (sig[i.val]).2
    else leaf)

/-! ### Correctness -/

/-- **FORS+C correctness**: recovering the FORS+C public key from an honest signature reproduces
`forsPkGen`, provided the digest's last index is forced to `0`. -/
theorem forsCPkFromSig_forsCSign (prims : Primitives) (digest : ℕ) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (hfz : forsIdx digest (params.k - 1) = 0) :
    forsCPkFromSig prims (forsCSign prims digest sk pk adrs) digest pk adrs
      = forsPkGen prims sk pk adrs := by
  unfold forsCPkFromSig forsPkGen
  refine congrArg (prims.Tl pk (forsPkAdrs adrs)) (List.map_congr_left fun i _ => ?_)
  simp only [forsCSign, Vector.getElem_ofFn]
  by_cases h : i.val < params.k - 1
  · simp only [if_pos h]
    have ht : (i.val * 2 ^ params.a + forsIdx digest i.val) / 2 ^ params.a = i.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ params.a),
        Nat.div_eq_of_lt (forsIdx_lt digest i.val), Nat.zero_add]
    have key := climb_authPath (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs)
      params.a 0 (i.val * 2 ^ params.a + forsIdx digest i.val)
    rw [Nat.zero_add, ht] at key
    exact key
  · have hik : i.val = params.k - 1 := by omega
    rw [if_neg h, if_neg h]
    simp only [hik, hfz, Nat.add_zero, forsLeaf]

end SLHDSA.C13
