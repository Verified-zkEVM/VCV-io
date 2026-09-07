/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Hypertree

/-!
# Oracle-parametric hypertree canaries

These examples cover the two observable contracts of the `d = 1` hypertree layer: signing is
transparent XMSS composition, and verification recovers a root before its final comparison.
-/

@[expose] public section

namespace SLHDSA.HypertreeTest

open OracleComp

variable {p : Params} (hd : p.d = 1) (core : CorePrimitives p)

/-- The canonical hypertree signer is exactly the addressed XMSS signer. -/
example (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    (htSignM core hd msg sk pk adrs idxTree idxLeaf :
      OracleComp (publicHashSpec core) (HtSigCore p core)) =
    (do
      let sig ← xmssSignM core msg sk pk (htAdrs adrs idxTree) idxLeaf
      return HtSigCore.singleLayer hd sig) := rfl

/-- Verification exposes recovery before the final pure comparison. -/
example [DecidableEq core.Y] (msg : core.Y) (sig : HtSigCore p core)
    (pk : core.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    (htVerifyM core hd msg sig pk adrs idxTree idxLeaf pkRoot :
      OracleComp (publicHashSpec core) Bool) = (do
        let recovered ← htPkFromSigM core hd msg sig pk adrs idxTree idxLeaf
        return decide (recovered = pkRoot)) := by
  rfl

/-- A single-layer wrapper stores exactly one XMSS signature, rather than repeating it through
the vector representation. -/
example (sig : XmssSigCore p core) : (HtSigCore.singleLayer hd sig).toList = [sig] := by
  change (Vector.ofFn fun _ : Fin p.d => sig).toList = [sig]
  rw [hd]
  simp only [Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero]

/-- The single-layer projections form a round trip for every vector admitted by the intrinsic
representation, rather than only for signatures first built by `singleLayer`. -/
example (sig : HtSigCore p core) :
    HtSigCore.singleLayer hd (HtSigCore.getSingleLayer hd sig) = sig :=
  HtSigCore.singleLayer_getSingleLayer hd sig

/-- The exported equivalence exposes both compatibility directions through one reusable API. -/
example (sig : XmssSigCore p core) :
    (HtSigCore.singleLayerEquiv hd).symm sig = HtSigCore.singleLayer hd sig := rfl

/-- The equivalence's inverse round trip is definitionally the explicit single-layer wrapper. -/
example (sig : HtSigCore p core) :
    (HtSigCore.singleLayerEquiv hd).symm (HtSigCore.singleLayerEquiv hd sig) = sig := by
  exact (HtSigCore.singleLayerEquiv hd).symm_apply_apply sig

/-- A small two-layer arithmetic shape used to make layer order observable. -/
def twoLayerParams : Params :=
  { n := 1, h := 2, d := 2, hp := 1, a := 1, k := 1, lgw := 1 }

/-- Construct a two-layer hypertree signature with intentionally distinguishable components. -/
def twoLayerSig (core : CorePrimitives twoLayerParams)
    (lower upper : XmssSigCore twoLayerParams core) : HtSigCore twoLayerParams core :=
  Vector.ofFn fun i => if i.val = 0 then lower else upper

/-- Intrinsic hypertree vectors retain each layer and its order. This rejects replacing the
representation with a duplicated singleton or swapping layer traversal order. -/
example (core : CorePrimitives twoLayerParams) (lower upper : XmssSigCore twoLayerParams core)
    (hne : lower ≠ upper) :
    (twoLayerSig core lower upper).toList = [lower, upper] ∧
      (twoLayerSig core lower upper)[0]'(by decide) = lower ∧
      (twoLayerSig core lower upper)[1]'(by decide) = upper ∧
      (twoLayerSig core lower upper)[0]'(by decide) ≠
        (twoLayerSig core lower upper)[1]'(by decide) := by
  change
    (Vector.ofFn fun i : Fin 2 => if i.val = 0 then lower else upper).toList = [lower, upper] ∧
      (Vector.ofFn fun i : Fin 2 => if i.val = 0 then lower else upper)[0]'(by decide) = lower ∧
      (Vector.ofFn fun i : Fin 2 => if i.val = 0 then lower else upper)[1]'(by decide) = upper ∧
      (Vector.ofFn fun i : Fin 2 => if i.val = 0 then lower else upper)[0]'(by decide) ≠
        (Vector.ofFn fun i : Fin 2 => if i.val = 0 then lower else upper)[1]'(by decide)
  simp only [Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero]
  simp [hne]

/-- A named FIPS shape is multi-layer and therefore cannot satisfy the compatibility premise
required by the present wrappers. Its signature representation nevertheless records all layers. -/
example (core : CorePrimitives (.SLHDSA_SHA2_128s : FipsParameterSet).params)
    (sig : HtSigCore (.SLHDSA_SHA2_128s : FipsParameterSet).params core) :
    sig.toList.length = 7 ∧
      ¬(.SLHDSA_SHA2_128s : FipsParameterSet).params.d = 1 := by
  constructor
  · simpa [FipsParameterSet.params] using (Vector.length_toList (xs := sig))
  · decide

end SLHDSA.HypertreeTest
