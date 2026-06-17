/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Xmss

/-!
# FORS (FIPS 205 §8)

The few-time forest signature: `k` Merkle trees of height `a`, with leaves `F(secret)` and the
`k` roots compressed by `T_k`. Reuses the generic Merkle theory of `HashSig.SLHDSA.Xmss`
(`SLHDSA.Merkle`). Provides `forsSkGen`/`forsLeaf`/`forsRoot` (Algorithms 14–15), `forsSign`
(Algorithm 16), `forsPkFromSig` (Algorithm 17), and the correctness lemma
`forsPkFromSig_forsSign`: recovery from an honest FORS signature reproduces the FORS public key.

Because the FORS public key compresses the *whole-tree* roots (which are message-independent),
`forsPkFromSig (forsSign md) md = forsPkGen` holds for every digest `md`.

## References

- NIST FIPS 205, §8 (Algorithms 14–17)
-/


namespace SLHDSA

variable {p : Params}

/-! ### FORS leaf indices -/

/-- The selected leaf index in FORS tree `i`: the `i`-th base-`2^a` digit of the digest. -/
def forsIdx (p : Params) (md : List Byte) (i : ℕ) : ℕ := (base2b md p.a p.k).getD i 0

theorem forsIdx_lt (p : Params) (md : List Byte) (i : ℕ) : forsIdx p md i < 2 ^ p.a := by
  unfold forsIdx
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i (base2b md p.a p.k).length with h | h
  · rw [List.getElem?_eq_getElem h]
    simpa using base2b_lt md p.a p.k _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]
    simp only [Option.getD_none]
    positivity

/-! ### FORS addresses, secret values, leaves, and tree roots -/

/-- Address for the FORS secret value at global leaf index `t` (type `FORS_PRF`). -/
def forsSkAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .forsPrf).setKeyPairAddress adrs.getKeyPairAddress).setTreeIndex t

/-- The FORS secret value at global leaf index `t` (FIPS 205 Algorithm 14). -/
def forsSkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  prims.PRF pk sk (forsSkAdrs adrs t)

/-- Address for the FORS-tree node at `(height z, global index t)` (type `FORS_TREE`). -/
def forsNodeAdrs (adrs : Adrs) (z t : ℕ) : Adrs :=
  let base := (adrs.setTypeAndClear .forsTree).setKeyPairAddress adrs.getKeyPairAddress
  (base.setTreeHeight z).setTreeIndex t

/-- The FORS leaf value at global index `t`: `F` of the secret value. -/
def forsLeaf (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  prims.F pk (forsNodeAdrs adrs 0 t) (forsSkGen prims sk pk adrs t)

/-- The FORS internal-node hash at `(height z, global index t)`. -/
def forsNodeHash (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  prims.H pk (forsNodeAdrs adrs z t) l r

/-- The root of FORS tree `i` (the height-`a` node at index `i`; FIPS 205 Algorithm 15). -/
def forsRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (i : ℕ) : prims.Y :=
  Merkle.merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a i

/-- Address compressing the `k` FORS roots into the FORS public key (type `FORS_ROOTS`). -/
def forsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .forsRoots).setKeyPairAddress adrs.getKeyPairAddress

/-- The FORS public key: `T_k` of the `k` tree roots (message-independent). -/
def forsPkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  prims.Tl pk (forsPkAdrs adrs)
    ((List.finRange p.k).map fun i => forsRoot prims sk pk adrs i.val)

/-! ### Signing and recovery -/

/-- A FORS signature: per tree, the revealed leaf secret and its `a`-node authentication path. -/
abbrev ForsSig (p : Params) (prims : Primitives p) := Vector (prims.Y × List prims.Y) p.k

/-- FORS signing (FIPS 205 Algorithm 16): reveal the selected leaf secret and auth path per
tree. -/
def forsSign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : ForsSig p prims :=
  Vector.ofFn fun i : Fin p.k =>
    (forsSkGen prims sk pk adrs (i.val * 2 ^ p.a + forsIdx p md i.val),
      Merkle.authPath (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) 0
        (i.val * 2 ^ p.a + forsIdx p md i.val) p.a)

/-- FORS public-key recovery from a signature (FIPS 205 Algorithm 17): recompute each tree's
leaf and climb its auth path, then compress the `k` recovered roots with `T_k`. -/
def forsPkFromSig (prims : Primitives p) (sig : ForsSig p prims) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  prims.Tl pk (forsPkAdrs adrs) ((List.finRange p.k).map fun i =>
    Merkle.climb (forsNodeHash prims pk adrs) 0 (i.val * 2 ^ p.a + forsIdx p md i.val)
      (prims.F pk (forsNodeAdrs adrs 0 (i.val * 2 ^ p.a + forsIdx p md i.val)) (sig[i.val]).1)
      (sig[i.val]).2)

/-! ### Correctness -/

/-- **FORS correctness** (FIPS 205, Algorithms 14–17): recovering the FORS public key from an
honest signature reproduces `forsPkGen`. Each tree's recovered root equals its true root by the
Merkle auth-path consistency lemma. -/
theorem forsPkFromSig_forsSign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSig prims (forsSign prims md sk pk adrs) md pk adrs = forsPkGen prims sk pk adrs := by
  unfold forsPkFromSig forsPkGen
  refine congrArg (prims.Tl pk (forsPkAdrs adrs)) (List.map_congr_left fun i _ => ?_)
  simp only [forsSign, Vector.getElem_ofFn]
  have ht : (i.val * 2 ^ p.a + forsIdx p md i.val) / 2 ^ p.a = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ p.a),
      Nat.div_eq_of_lt (forsIdx_lt p md i.val), Nat.zero_add]
  have key := Merkle.climb_authPath (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs)
    p.a 0 (i.val * 2 ^ p.a + forsIdx p md i.val)
  rw [Nat.zero_add, ht] at key
  exact key

end SLHDSA
