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

An SLH-DSA security reduction issues one distinct-target hash challenge per reachable address in
each hash role.  This module names those roles and gives the closed formulas for the number of
targets each role can reach in a hypertree with `d` layers of height `hp`:

- `treesAtLayer p i = 2 ^ (hp * (d - i - 1))` XMSS trees at layer `i`;
- `xmssTreeCount p` XMSS trees in total and `wotsInstanceCount p` WOTS+ instances in total;
- `targetCount p role` for each of the eight `TargetRole`s.

The counts are pure parameter arithmetic.  `HashSig.SLHDSA.Security.ReachableTargets` realizes
each of them by an executable, duplicate-free address ledger.  Six of the eight are realized
exactly.  The two that are not are upper bounds in the safe direction:

- `wotsFTcr` counts `w` steps per WOTS+ chain, while a chain executes only the `w - 1` steps its
  ledger lists; the source proof's looser cap is kept so the term matches the literature; and
- `wotsFPre` counts one step per chain, while a preimage reduction may omit the chains whose
  honest digit is zero.

Every count is the one the machine-checked source proof issues.  In its artifact the FORS roles are
`t_smdtopenpre = d * k * t`, which the OpenPRE-from-collision-and-second-preimage theory forwards to
those two games as its own `t`, then `t_smdttcr = d * k * (t - 1)` for the node hash and
`t_smdttcr = d` for the root compression; the three WOTS+ `F` roles are `t_smdtud = t_smdtpre =
c * len` and `t_smdttcr = c * len * w`; and `wotsTl` and `xmssH` are the two hypertree sums.  The
name `t_smdttcr` is reused across those theories, so each is read in its own.  The FORS-instance
variable `d` instantiates to `2 ^ h`, the number of bottom-layer leaves, not to the layer count
`Params.d`, and `c` is `wotsInstanceCount`.

## References

- NIST FIPS 205, §4.1, §10
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified"
-/

@[expose] public section

namespace SLHDSA.Security

/-! ## Closed target-role vocabulary -/

/-- The eight distinct-target hash roles of the classical SLH-DSA security argument.  The WOTS+
`F` role appears three times because its three games select their targets differently: the
undetectability game takes one step per chain and the preimage game at most one, while the
target-collision game ranges over every step of every chain. -/
inductive TargetRole
  /-- FORS leaf hash `F` (arity one). -/
  | forsF
  /-- FORS internal-node hash `H` (arity two). -/
  | forsH
  /-- FORS root compression `T_k`. -/
  | forsTl
  /-- WOTS+ chain hash `F`, undetectability targets (one selected step per chain). -/
  | wotsFUd
  /-- WOTS+ chain hash `F`, target-collision-resistance targets (every step of every chain). -/
  | wotsFTcr
  /-- WOTS+ chain hash `F`, preimage targets (at most one selected step per chain). -/
  | wotsFPre
  /-- WOTS+ public-key compression `T_len`. -/
  | wotsTl
  /-- XMSS internal-node hash `H`. -/
  | xmssH
  deriving DecidableEq, Repr

instance : Fintype TargetRole where
  elems := {.forsF, .forsH, .forsTl, .wotsFUd, .wotsFTcr, .wotsFPre, .wotsTl, .xmssH}
  complete role := by cases role <;> simp

@[simp] theorem TargetRole.card : Fintype.card TargetRole = 8 := by decide

/-! ## Tree and instance counts -/

/-- The number of XMSS trees at hypertree layer `i`: the top layer has one tree and each lower
layer has `2 ^ hp` times as many. -/
def treesAtLayer (p : Params) (i : Fin p.d) : ℕ :=
  2 ^ (p.hp * (p.d - i.val - 1))

/-- The total number of XMSS trees across all hypertree layers. -/
def xmssTreeCount (p : Params) : ℕ :=
  ∑ i : Fin p.d, treesAtLayer p i

/-- The total number of WOTS+ instances: every XMSS tree has `2 ^ hp` leaves. -/
def wotsInstanceCount (p : Params) : ℕ :=
  ∑ i : Fin p.d, treesAtLayer p i * 2 ^ p.hp

/-- Formula-derived cap on the number of targets issued in each named game.  Six roles meet their
cap exactly; `wotsFTcr` and `wotsFPre` are upper bounds, as the module docstring records. -/
def targetCount (p : Params) : TargetRole → ℕ
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

/-- The undetectability and preimage roles share the one-target-per-WOTS+-chain cap.  The
orientation keeps `selectedWotsAddresses_length` in simp-normal form, since that lemma names the
undetectability role. -/
@[simp] theorem targetCount_wotsFPre_eq_wotsFUd (p : Params) :
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
