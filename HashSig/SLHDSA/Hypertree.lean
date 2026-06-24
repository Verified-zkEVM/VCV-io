/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Fors

/-!
# Hypertree (FIPS 205 §7)

For the SLH-DSA-SHA2-128-24 parameter set `d = 1`, so the hypertree is a **single** XMSS tree
and `ht_sign` / `ht_verify` (Algorithms 12–13) collapse to one XMSS layer. This module gives
that single-layer instantiation (`htSign`, `htVerify`, `htRoot`) and the correctness lemma
`htVerify_htSign`, derived directly from XMSS correctness (`xmssPkFromSig_xmssSign`).

The general `d > 1` hypertree (each layer WOTS-signs the root of the layer below; needed by the
C13 parameter set) is a future generalization of `HtSig` to a `d`-element layer list with a
fold; it is intentionally out of scope here so the `d = 1` development stays fully proved.

## References

- NIST FIPS 205, §7 (Algorithms 12–13)
-/


namespace SLHDSA

variable {p : Params}

/-- A hypertree signature for `d = 1`: a single XMSS signature of the FORS public key. -/
abbrev HtSig (p : Params) (prims : Primitives p) := XmssSig p prims

/-- The address of the single hypertree layer (layer `0`, tree `idxTree`). -/
private def htAdrs (adrs : Adrs) (idxTree : ℕ) : Adrs :=
  (adrs.setLayerAddress 0).setTreeAddress idxTree

/-- Hypertree signing for `d = 1` (FIPS 205 Algorithm 12): XMSS-sign `msg` at the chosen leaf
of the single tree. -/
def htSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) : HtSig p prims :=
  xmssSign prims msg sk pk (htAdrs adrs idxTree) idxLeaf

/-- The hypertree root committed by key generation (`d = 1`: the single XMSS tree root). -/
def htRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (idxTree : ℕ) : prims.Y :=
  xmssRoot prims sk pk (htAdrs adrs idxTree)

/-- Hypertree verification for `d = 1` (FIPS 205 Algorithm 13): recover the XMSS root from the
signature and compare it to the public root. -/
def htVerify (prims : Primitives p) [DecidableEq prims.Y] (msg : prims.Y) (sig : HtSig p prims)
    (pk : prims.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : prims.Y) : Bool :=
  decide (xmssPkFromSig prims idxLeaf sig msg pk (htAdrs adrs idxTree) = pkRoot)

/-- **Hypertree correctness** for `d = 1` (FIPS 205, Algorithms 12–13): verification of an
honest hypertree signature against the key-generation root succeeds. -/
theorem htVerify_htSign (prims : Primitives p) [DecidableEq prims.Y] (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ)
    (hidx : idxLeaf < 2 ^ p.hp) :
    htVerify prims msg (htSign prims msg sk pk adrs idxTree idxLeaf) pk adrs idxTree idxLeaf
        (htRoot prims sk pk adrs idxTree) = true := by
  unfold htVerify htSign htRoot
  rw [xmssPkFromSig_xmssSign prims msg sk pk (htAdrs adrs idxTree) idxLeaf hidx]
  simp

end SLHDSA
