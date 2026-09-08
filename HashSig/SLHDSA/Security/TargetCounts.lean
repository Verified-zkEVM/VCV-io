/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Alexander Hicks
-/

module
public import HashSig.SLHDSA.Params
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum

/-!
# SLH-DSA security target roles and formula-derived target counts

The classical SLH-DSA security proof uses upper bounds on the number of distinct-target hash
challenges in each hash role.  This module names those roles and gives the closed formulas for
their caps in a hypertree with `d` layers of height `hp`:

- `treesAtLayer p i = 2 ^ (hp * (d - i - 1))` XMSS trees at layer `i`;
- `xmssTreeCount p` XMSS trees in total and `wotsInstanceCount p` WOTS+ instances in total;
- `targetCount p role` for each of the eight `TargetRole`s.

The counts are pure parameter arithmetic.  `HashSig.SLHDSA.Security.ReachableTargets` relates
them to executable, duplicate-free structural address ledgers.  Five complete ledgers have exactly
the corresponding count.  The WOTS+ roles require the following qualifications:

- `wotsFUd` is a cap of one target per chain.  The source reduction's target list is partial: at
  hybrid index `j` it omits a chain unless `j < digit - 1`.  The total-selection ledger is a
  duplicate-free completion used to witness the cap, not the reduction's exact target list;
- `wotsFTcr` counts `w` steps per WOTS+ chain, while a chain executes only the `w - 1` steps its
  ledger lists; the source proof's looser cap is kept so the term matches the literature; and
- `wotsFPre` counts one step per chain, while a preimage reduction may omit the chains whose
  honest digit is zero.

Every count is the cap instantiated by the machine-checked source proof.  In its artifact the FORS
leaf hash
carries `t_smdtopenpre = d * k * t`, which the OpenPRE-from-TCR-and-DSPR reduction forwards
unchanged as the target count of the SM-DT-TCR and SM-DT-DSPR games it reduces to; the FORS node
hash carries `t_smdttcr = d * k * (t - 1)` and the root compression `t_smdttcr = d`; the three
WOTS+ `F` roles carry `t_smdtud = t_smdtpre = c * len` and `t_smdttcr = c * len * w`; and `wotsTl`
and `xmssH` carry the two hypertree sums.  `t_smdttcr` names the target count of whichever
collision game its own theory clones, so each occurrence is read in that theory.  The FORS-instance
variable `d` instantiates to `2 ^ h`, the number of bottom-layer leaves, not to the layer count
`Params.d`, and `c` is `wotsInstanceCount`.  The Lean module
`VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.OpenPREFromTCRDSPR` formalizes that
reduction; the EasyCrypt theory is `OpenPRE_From_TCR_DSPR_THF`.

## References

- NIST FIPS 205, §4.1 (the hash roles), §5 (WOTS+ `len` and `w`), §7 (the hypertree layers and
  `h = d · h'`), §8 (FORS `k` and `t = 2^a`)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
- EasyCrypt artifact `MM45/FV-SPHINCSPLUS-EC`, commit `a28e4c53897a4bb57b575a177225862d48f824b7`
  (`proofs/WOTS_TW_ES.ec`, `proofs/FORS_ES.ec`, and `proofs/FL_SL_XMSS_MT_ES.ec`)
-/

public section

namespace SLHDSA.Security

/-! ## Closed target-role vocabulary -/

/-- The eight distinct-target hash roles of the classical SLH-DSA security argument.  The WOTS+
`F` role appears three times because its three games select their targets differently: the
undetectability and preimage games take at most one step per chain, under different selection
rules, while the target-collision game takes a suffix of up to `w - 1` executable steps per
chain. -/
inductive TargetRole
  /-- FORS leaf hash `F` (arity one). -/
  | forsF
  /-- FORS internal-node hash `H` (arity two). -/
  | forsH
  /-- FORS root compression `T_k`. -/
  | forsTl
  /-- WOTS+ chain hash `F`, undetectability targets (at most one selected step per chain). -/
  | wotsFUd
  /-- WOTS+ chain hash `F`, target-collision-resistance cap (all executable chain steps). -/
  | wotsFTcr
  /-- WOTS+ chain hash `F`, preimage targets (at most one selected step per chain). -/
  | wotsFPre
  /-- WOTS+ public-key compression `T_len`. -/
  | wotsTl
  /-- XMSS internal-node hash `H`. -/
  | xmssH
  deriving DecidableEq, Repr

-- Hand-rolled rather than `deriving Fintype`: on this toolchain the enum derive handler's
-- `enumList` coercion to `Multiset` is rejected under the `.implicit` transparency check.
instance : Fintype TargetRole where
  elems := {.forsF, .forsH, .forsTl, .wotsFUd, .wotsFTcr, .wotsFPre, .wotsTl, .xmssH}
  complete role := by cases role <;> simp

@[simp] theorem TargetRole.card : Fintype.card TargetRole = 8 := by decide

/-! ## Tree and instance counts -/

/-- The number of XMSS trees at hypertree layer `i`: the top layer has one tree and each lower
layer has `2 ^ hp` times as many. -/
@[expose] def treesAtLayer (p : Params) (i : Fin p.d) : ℕ :=
  2 ^ (p.hp * (p.d - i.val - 1))

/-- The total number of XMSS trees across all hypertree layers. -/
@[expose] def xmssTreeCount (p : Params) : ℕ :=
  ∑ i : Fin p.d, treesAtLayer p i

/-- The total number of WOTS+ instances: every XMSS tree has `2 ^ hp` leaves. -/
@[expose] def wotsInstanceCount (p : Params) : ℕ :=
  ∑ i : Fin p.d, treesAtLayer p i * 2 ^ p.hp

/-- Formula-derived cap on the number of targets issued in each named game.  Five complete
structural ledgers have exactly the corresponding cap.  The `wotsFUd` cap has an exact total
completion but a potentially smaller source list; `wotsFTcr` and `wotsFPre` are upper bounds, as
the module docstring records. -/
@[expose] def targetCount (p : Params) : TargetRole → ℕ
  | .forsF => 2 ^ p.h * p.k * 2 ^ p.a
  | .forsH => 2 ^ p.h * p.k * (2 ^ p.a - 1)
  | .forsTl => 2 ^ p.h
  | .wotsFUd => wotsInstanceCount p * p.len
  | .wotsFTcr => wotsInstanceCount p * p.len * p.w
  | .wotsFPre => wotsInstanceCount p * p.len
  | .wotsTl => wotsInstanceCount p
  | .xmssH => xmssTreeCount p * (2 ^ p.hp - 1)

theorem wotsInstanceCount_eq_xmssTreeCount_mul (p : Params) :
    wotsInstanceCount p = xmssTreeCount p * 2 ^ p.hp := by
  unfold wotsInstanceCount xmssTreeCount
  exact (Finset.sum_mul _ _ _).symm

/-- The per-layer tree count as a power of the per-layer leaf count. -/
theorem treesAtLayer_eq_pow (p : Params) (i : Fin p.d) :
    treesAtLayer p i = (2 ^ p.hp) ^ (p.d - i.val - 1) := by
  rw [treesAtLayer, pow_mul]

/-- Summing the per-layer tree counts from the top layer down gives an ordinary geometric sum in
the per-layer leaf count. -/
theorem xmssTreeCount_eq_geomSum (p : Params) :
    xmssTreeCount p = ∑ i ∈ Finset.range p.d, (2 ^ p.hp) ^ i := by
  unfold xmssTreeCount treesAtLayer
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ (p.hp * (p.d - i - 1))),
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [pow_mul]
  congr 1
  omega

/-- The XMSS trees of a hypertree contain exactly `2 ^ h - 1` internal nodes in total. -/
theorem xmssTreeCount_mul_pred (p : Params) (hvalid : p.Valid) :
    xmssTreeCount p * (2 ^ p.hp - 1) = 2 ^ p.h - 1 := by
  have hpos : 1 ≤ 2 ^ p.hp := Nat.one_le_two_pow
  have hgeom := geom_sum_mul_add (2 ^ p.hp - 1) p.d
  rw [Nat.sub_add_cancel hpos] at hgeom
  rw [xmssTreeCount_eq_geomSum, hvalid.h_eq_layers, pow_mul']
  omega

theorem targetCount_xmssH_eq (p : Params) (hvalid : p.Valid) :
    targetCount p .xmssH = 2 ^ p.h - 1 :=
  xmssTreeCount_mul_pred p hvalid

/-- The undetectability and preimage roles share the one-target-per-WOTS+-chain cap, so a bound
proved for either transfers to the other.  This is deliberately not a simp lemma: either
orientation would take one of the two role names out of simp-normal form. -/
theorem targetCount_wotsFPre_eq_wotsFUd (p : Params) :
    targetCount p .wotsFPre = targetCount p .wotsFUd := rfl

/-! ## Positivity -/

theorem xmssTreeCount_pos (p : Params) (hvalid : p.Valid) : 0 < xmssTreeCount p := by
  unfold xmssTreeCount
  apply Finset.sum_pos'
  · intro i _
    exact Nat.zero_le _
  · exact ⟨⟨0, hvalid.d_pos⟩, Finset.mem_univ _, Nat.two_pow_pos _⟩

theorem wotsInstanceCount_pos (p : Params) (hvalid : p.Valid) : 0 < wotsInstanceCount p := by
  rw [wotsInstanceCount_eq_xmssTreeCount_mul]
  exact Nat.mul_pos (xmssTreeCount_pos p hvalid) (Nat.two_pow_pos _)

theorem targetCount_pos (p : Params) (hvalid : p.Valid) (role : TargetRole) :
    0 < targetCount p role := by
  have ha : 0 < 2 ^ p.a - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hvalid.a_pos))
  have hhp : 0 < 2 ^ p.hp - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hvalid.hp_pos))
  have hw := wotsInstanceCount_pos p hvalid
  cases role with
  | forsF => exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hvalid.k_pos) (Nat.two_pow_pos _)
  | forsH => exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hvalid.k_pos) ha
  | forsTl => exact Nat.two_pow_pos _
  | wotsFUd => exact Nat.mul_pos hw p.len_pos
  | wotsFTcr => exact Nat.mul_pos (Nat.mul_pos hw p.len_pos) (Nat.two_pow_pos _)
  | wotsFPre => exact Nat.mul_pos hw p.len_pos
  | wotsTl => exact hw
  | xmssH => exact Nat.mul_pos (xmssTreeCount_pos p hvalid) hhp

/-! ## One-layer specialization -/

/-- At `d = 1` the hypertree is a single XMSS tree. -/
theorem xmssTreeCount_of_d_eq_one (p : Params) (hd : p.d = 1) : xmssTreeCount p = 1 := by
  unfold xmssTreeCount treesAtLayer
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ (p.hp * (p.d - i - 1))), hd]
  simp

/-- At `d = 1` every leaf of the single XMSS tree is a WOTS+ instance. -/
theorem wotsInstanceCount_of_d_eq_one (p : Params) (hd : p.d = 1) :
    wotsInstanceCount p = 2 ^ p.hp := by
  rw [wotsInstanceCount_eq_xmssTreeCount_mul, xmssTreeCount_of_d_eq_one p hd, one_mul]

end SLHDSA.Security
