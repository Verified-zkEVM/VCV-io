/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.C13.Xmss

/-!
# C13 hypertree (d = 2)

The two-layer hypertree of C13 (`h = 22 = 2·h'`, `h' = 11`). The 22-bit hypertree index
`htIdx` splits into a bottom-layer `(tree, leaf)` and a top-layer `(tree = 0, leaf)`; layer 0
WOTS+C-signs the FORS+C public key, layer 1 signs the layer-0 XMSS root, and the layer-1 root is
the public root. `htVerify_htSign` proves that verification of an honest hypertree signature
against the key-generation root succeeds, for any `htIdx < 2^h`, composing XMSS+C correctness
across the two layers. (The WOTS+C fixed-sum gates are verifier checks applied in the top-level
scheme, not part of this root-reconstruction lemma.)

## References

- NIST FIPS 205 §7 (hypertree); the SPHINCs- repo verifier `src/SPHINCs-C13Asm.sol`
-/


namespace SLHDSA.C13

open SLHDSA (Adrs)

/-! ### Hypertree index decomposition -/

/-- Bottom-layer leaf index: low `h'` bits of `htIdx`. -/
def htLeaf0 (htIdx : ℕ) : ℕ := htIdx % 2 ^ params.hp
/-- Bottom-layer tree index: `htIdx ≫ h'`. -/
def htTree0 (htIdx : ℕ) : ℕ := htIdx / 2 ^ params.hp
/-- Top-layer leaf index. -/
def htLeaf1 (htIdx : ℕ) : ℕ := htTree0 htIdx % 2 ^ params.hp
/-- Top-layer tree index (`0` for valid `htIdx`). -/
def htTree1 (htIdx : ℕ) : ℕ := htTree0 htIdx / 2 ^ params.hp

/-- Address for layer `layer`, tree `tree`. -/
def layerAdrs (layer tree : ℕ) : Adrs := (Adrs.zero.setLayerAddress layer).setTreeAddress tree

/-- The hypertree root committed by key generation: the top-layer single-tree XMSS root. -/
def htRoot (prims : Primitives) (sk : prims.SkSeed) (pk : prims.PkSeed) : prims.Y :=
  xmssRoot prims sk pk (layerAdrs 1 0)

/-- A C13 hypertree signature: the two XMSS+C layer signatures. -/
abbrev HtSig (prims : Primitives) := XmssSig prims × XmssSig prims

/-- Hypertree signing (`d = 2`): layer 0 signs `forsPk`, layer 1 signs the layer-0 root. -/
def htSign (prims : Primitives) (forsPk : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (htIdx count0 count1 : ℕ) : HtSig prims :=
  let sig0 := xmssSign prims forsPk sk pk (layerAdrs 0 (htTree0 htIdx)) (htLeaf0 htIdx) count0
  let root0 := xmssRoot prims sk pk (layerAdrs 0 (htTree0 htIdx))
  (sig0, xmssSign prims root0 sk pk (layerAdrs 1 (htTree1 htIdx)) (htLeaf1 htIdx) count1)

/-- The WOTS+C base address signing the value at hypertree layer `layer` (key-pair = the
layer's leaf index), against which that layer's fixed digit-sum gate is checked. -/
def htWotsAdrs (layer htIdx : ℕ) : Adrs :=
  if layer = 0 then wotsLeafAdrs (layerAdrs 0 (htTree0 htIdx)) (htLeaf0 htIdx)
  else wotsLeafAdrs (layerAdrs 1 (htTree1 htIdx)) (htLeaf1 htIdx)

/-- Hypertree verification (`d = 2`): enforce each layer's WOTS+C fixed digit-sum gate
(`SPHINCs-C13Asm.sol`: `digitSum == targetSum`), then climb both layers and compare to the
public root. -/
def htVerify (prims : Primitives) [DecidableEq prims.Y] (forsPk : prims.Y) (sig : HtSig prims)
    (pk : prims.PkSeed) (htIdx : ℕ) (pkRoot : prims.Y) : Bool :=
  let node0 := xmssPkFromSig prims (htLeaf0 htIdx) sig.1 forsPk pk (layerAdrs 0 (htTree0 htIdx))
  let node1 := xmssPkFromSig prims (htLeaf1 htIdx) sig.2 node0 pk (layerAdrs 1 (htTree1 htIdx))
  digitSumOk prims pk (htWotsAdrs 0 htIdx) forsPk sig.1.2.1
    && digitSumOk prims pk (htWotsAdrs 1 htIdx) node0 sig.2.2.1
    && decide (node1 = pkRoot)

/-- **C13 hypertree correctness** (`d = 2`): verification of an honest hypertree signature
against the key-generation root succeeds, for any `htIdx < 2^h`, **provided each layer's WOTS+C
counter grinds the digits to `targetSum`** (the `digitSum_* = targetSum` hypotheses, the
verifier-side gate the grind establishes; the forced-zero analogue of `slhSignInternal`). -/
theorem htVerify_htSign (prims : Primitives) [DecidableEq prims.Y] (forsPk : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (htIdx count0 count1 : ℕ)
    (hHt : htIdx < 2 ^ params.h)
    (hd0 : digitSum prims pk (htWotsAdrs 0 htIdx) forsPk count0 = targetSum)
    (hd1 : digitSum prims pk (htWotsAdrs 1 htIdx)
      (xmssRoot prims sk pk (layerAdrs 0 (htTree0 htIdx))) count1 = targetSum) :
    htVerify prims forsPk (htSign prims forsPk sk pk htIdx count0 count1) pk htIdx
        (htRoot prims sk pk) = true := by
  unfold htVerify htSign htRoot
  dsimp only
  rw [xmssPkFromSig_xmssSign prims forsPk sk pk (layerAdrs 0 (htTree0 htIdx)) (htLeaf0 htIdx)
    count0 (Nat.mod_lt _ (by positivity))]
  rw [xmssPkFromSig_xmssSign prims (xmssRoot prims sk pk (layerAdrs 0 (htTree0 htIdx))) sk pk
    (layerAdrs 1 (htTree1 htIdx)) (htLeaf1 htIdx) count1 (Nat.mod_lt _ (by positivity))]
  have hh : params.h = params.hp + params.hp := by decide
  have h0 : htTree0 htIdx < 2 ^ params.hp := by
    unfold htTree0
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← hh]
    exact hHt
  have ht1 : htTree1 htIdx = 0 := by unfold htTree1; exact Nat.div_eq_of_lt h0
  rw [ht1]
  simp [xmssSign, digitSumOk, hd0, hd1]

end SLHDSA.C13
