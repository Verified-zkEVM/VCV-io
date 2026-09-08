/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import all LatticeCrypto.MLDSA.Concrete.Encoding
import LatticeCrypto.MLDSA.Concrete.LawBounds
public import Extern.Hashing
public import LatticeCrypto.MLDSA.Concrete.Encoding
public import LatticeCrypto.MLDSA.Concrete.NTT

/-!
# Concrete Sampling and Hash Wiring for ML-DSA

This file instantiates the SHAKE-128 / SHAKE-256 based sampling and hashing algorithms used by
FIPS 204:

- `ExpandSeed`
- `SampleInBall`
- `ExpandA`
- `ExpandS`
- `ExpandMask`
- message / commitment hash wrappers
-/

public section


namespace MLDSA.Concrete

open MLDSA

/-! ## SHAKE helpers -/

private def nonceLE (nonce : Nat) : ByteArray :=
  ByteArray.mk #[nonce.toUInt8, (nonce / 256).toUInt8]

private def shake256Stream (seed : ByteArray) (nonce outLen : Nat) : ByteArray :=
  FFI.Hashing.shake256 (seed ++ nonceLE nonce) outLen.toUSize

/-- Materialize a SHAKE-256 output stream as a fixed-length byte vector. -/
def shake256Vector (input : ByteArray) (outLen : Nat) : Vector Byte outLen :=
  byteArrayToVector (FFI.Hashing.shake256 input outLen.toUSize) 0 outLen

/-- Hash a byte array to 64 bytes with SHAKE-256. -/
def hashBytes64 (input : ByteArray) : Bytes 64 :=
  shake256Vector input 64

/-! ## ExpandSeed -/

/-- FIPS 204 `ExpandSeed`, returning `(ρ, ρ', K)` from a 32-byte seed and the parameter tags. -/
def expandSeed (seed : Bytes 32) (p : Params) : Bytes 32 × Bytes 64 × Bytes 32 :=
  let input := vectorToByteArray seed |>.push p.k.toUInt8 |>.push p.l.toUInt8
  let out := FFI.Hashing.shake256 input 128
  (byteArrayToVector out 0 32, byteArrayToVector out 32 64, byteArrayToVector out 96 32)

/-! ## Uniform rejection sampling in `Tq` -/

/-- Fuel-bounded structural recursion replacing the `while` rejection loop of `rejUniformCoeffs`.
Each iteration reads three bytes at `pos`, forms the 23-bit candidate, pushes it when it is below
the modulus, and advances `pos` by 3. The loop guard
`coeffs.size < ringDegree ∧ pos + 3 ≤ stream.size`
is replicated exactly; `fuel` is decremented every iteration and a safe upper bound (`stream.size`)
guarantees the recursion never exhausts before the guard fails on valid inputs. -/
private def rejUniformCoeffsAux (stream : ByteArray) :
    Nat → Array Coeff → Nat → Array Coeff
  | 0, coeffs, _ => coeffs
  | fuel + 1, coeffs, pos =>
    if coeffs.size < ringDegree ∧ pos + 3 ≤ stream.size then
      let b0 := (getByteD stream pos).toNat
      let b1 := (getByteD stream (pos + 1)).toNat
      let b2 := (getByteD stream (pos + 2)).toNat
      let t := (b0 + Nat.shiftLeft b1 8 + Nat.shiftLeft b2 16) &&& 0x7FFFFF
      let coeffs := if t < modulus then coeffs.push (t : Coeff) else coeffs
      rejUniformCoeffsAux stream fuel coeffs (pos + 3)
    else
      coeffs

private def rejUniformCoeffs (stream : ByteArray) : Array Coeff :=
  rejUniformCoeffsAux stream stream.size (Array.mkEmpty ringDegree) 0

private def requireFullUniformSample (coeffs : Array Coeff) : Array Coeff :=
  if _h : coeffs.size = ringDegree then
    coeffs
  else
    panic! s!"ML-DSA uniform sampler produced {coeffs.size} coefficients; expected {ringDegree}"

/-- FIPS 204 Algorithm 30. -/
def rejNTTPoly (input : ByteArray) : Tq :=
  let stream := FFI.Hashing.shake128 input 4096
  let coeffs := requireFullUniformSample <| rejUniformCoeffs stream
  ⟨Vector.ofFn fun i => coeffs.getD i.val 0⟩

/-- FIPS 204 Algorithm 32: `ExpandA(ρ)`.
FIPS 204 specifies the input as `ρ ∥ IntegerToBytes(s, 1) ∥ IntegerToBytes(r, 1)` where
`r` is the row and `s` is the column. Since `nonceLE` writes in little-endian, passing
`row.val * 256 + col.val` produces the bytes `[col, row]` = `[s, r]` as required. -/
def expandA (rho : Bytes 32) (p : Params) : TqMatrix p.k p.l :=
  let rhoBytes := vectorToByteArray rho
  Vector.ofFn fun row =>
    Vector.ofFn fun col =>
      rejNTTPoly (rhoBytes ++ nonceLE (row.val * 256 + col.val))

/-! ## `η`-bounded secret sampling -/

/-- Body of one `rejEtaCoeffs` iteration: split the byte into two nibbles and conditionally push the
centered `η`-bounded values, re-checking the `ringDegree` capacity before each push exactly as the
original `while` body does. -/
private def rejEtaStep (eta : Nat) (byte : Nat) (coeffs : Array ℤ) : Array ℤ :=
  let t0 := byte &&& 0x0F
  let t1 := Nat.shiftRight byte 4
  if eta = 2 then
    let coeffs :=
      if t0 < 15 ∧ coeffs.size < ringDegree then
        let u0 := t0 - Nat.shiftRight (205 * t0) 10 * 5
        coeffs.push ((2 : ℤ) - (u0 : ℤ))
      else coeffs
    if t1 < 15 ∧ coeffs.size < ringDegree then
      let u1 := t1 - Nat.shiftRight (205 * t1) 10 * 5
      coeffs.push ((2 : ℤ) - (u1 : ℤ))
    else coeffs
  else if eta = 4 then
    let coeffs :=
      if t0 < 9 ∧ coeffs.size < ringDegree then
        coeffs.push ((4 : ℤ) - (t0 : ℤ))
      else coeffs
    if t1 < 9 ∧ coeffs.size < ringDegree then
      coeffs.push ((4 : ℤ) - (t1 : ℤ))
    else coeffs
  else coeffs

/-- Fuel-bounded structural recursion replacing the `while` rejection loop of `rejEtaCoeffs`. The
guard `coeffs.size < ringDegree ∧ pos < stream.size` and the per-iteration `pos` advance by 1 are
replicated exactly; `fuel := stream.size` is a safe upper bound. -/
private def rejEtaCoeffsAux (eta : Nat) (stream : ByteArray) :
    Nat → Array ℤ → Nat → Array ℤ
  | 0, coeffs, _ => coeffs
  | fuel + 1, coeffs, pos =>
    if coeffs.size < ringDegree ∧ pos < stream.size then
      let byte := (getByteD stream pos).toNat
      rejEtaCoeffsAux eta stream fuel (rejEtaStep eta byte coeffs) (pos + 1)
    else
      coeffs

private def rejEtaCoeffs (eta : Nat) (stream : ByteArray) : Array ℤ :=
  rejEtaCoeffsAux eta stream stream.size (Array.mkEmpty ringDegree) 0

private def requireFullEtaSample (coeffs : Array ℤ) : Array ℤ :=
  if _h : coeffs.size = ringDegree then
    coeffs
  else
    panic! s!"ML-DSA eta sampler produced {coeffs.size} coefficients; expected {ringDegree}"

def sampleEtaPoly (eta : Nat) (seed : Bytes 64) (nonce : Nat) : Rq :=
  let stream := shake256Stream (vectorToByteArray seed) nonce 1024
  let coeffs := requireFullEtaSample <| rejEtaCoeffs eta stream
  Vector.ofFn fun i => (coeffs.getD i.val 0 : Coeff)

/-- FIPS 204 Algorithm 33. -/
def expandS (rhoPrime : Bytes 64) (p : Params) : RqVec p.l × RqVec p.k :=
  let s1 : RqVec p.l := Vector.ofFn fun i => sampleEtaPoly p.eta rhoPrime i.val
  let s2 : RqVec p.k := Vector.ofFn fun i => sampleEtaPoly p.eta rhoPrime (p.l + i.val)
  (s1, s2)

/-! ## Mask expansion via `z` unpacking -/

/-- FIPS 204 Algorithm 34. -/
def expandMask (rhoPrime : Bytes 64) (kappa : ℕ) (p : Params) : RqVec p.l :=
  let seed := vectorToByteArray rhoPrime
  Vector.ofFn fun i =>
    polyZUnpack p <| shake256Stream seed (kappa + i.val) (polyZPackedBytes p)

/-- Every component produced by `expandMask` lies in the FIPS-204 `z` window for an approved
parameter set. -/
theorem expandMask_get_cInfNorm_le (p : Params) (hp : p.isApproved) (rhoPrime : Bytes 64)
    (kappa : ℕ) (j : Fin p.l) :
    LatticeCrypto.cInfNorm ((expandMask rhoPrime kappa p).get j) ≤ p.gamma1 := by
  obtain ⟨hwidth, hq⟩ := approved_gamma1_width p hp
  unfold expandMask
  rw [Vector.get_ofFn]
  exact bitUnpackPoly_z_cInfNorm_le _ p.gamma1 hwidth hq

/-! ## Challenge sampling -/

private def shake256Prefix (input : ByteArray) (len : Nat) : ByteArray :=
  FFI.Hashing.shake256 input len.toUSize

/-- Fuel-bounded structural recursion replacing the inner `while !found` rejection loop of
`sampleInBall`. Each iteration reads the byte at `pos`, advances `pos` by 1, and stops as soon as a
byte `b ≤ i` is found, returning that byte together with the next read position. The fixed
SHAKE stream used by `sampleInBall` is longer than the outer loop can consume before an
out-of-bounds read defaults to `0 ≤ i`; `fuel := stream.size` is therefore a safe bound for that
caller. -/
private def sampleInBallFindChosen (stream : ByteArray) (i : Nat) :
    Nat → Nat → Nat × Nat
  | 0, pos => (0, pos)
  | fuel + 1, pos =>
    let b := (getByteD stream pos).toNat
    if b ≤ i then
      (b, pos + 1)
    else
      sampleInBallFindChosen stream i fuel (pos + 1)

/-- Body of one outer `sampleInBall` iteration: find a byte `≤ i`, perform the Fisher–Yates style
swap-and-sign writes into the accumulator, and return the updated accumulator together with the
advanced read position and sign index. This replicates the original `while` body's array updates
exactly (`Array.set!` at index `i` then at index `chosen`). -/
private def sampleInBallStep (stream : ByteArray) (signs : Nat) (i : Nat)
    (out : Array Coeff) (pos signIdx : Nat) : Array Coeff × Nat × Nat :=
  let (chosen, pos) := sampleInBallFindChosen stream i stream.size pos
  let out := out.set! i (out.getD chosen 0)
  let sign := if ((signs / 2 ^ signIdx) % 2) = 0 then (1 : Coeff) else (-1 : Coeff)
  let out := out.set! chosen sign
  (out, pos, signIdx + 1)

/-- Fuel-bounded structural recursion replacing the outer `for i in [ringDegree - τ : ringDegree]`
loop of `sampleInBall`. It walks the indices `i = lo, lo + 1, …, hi - 1` in order, threading the
accumulator, read position, and sign index through `sampleInBallStep`. -/
private def sampleInBallLoop (stream : ByteArray) (signs hi : Nat) :
    Nat → Nat → Array Coeff → Nat → Nat → Array Coeff
  | 0, _, out, _, _ => out
  | fuel + 1, i, out, pos, signIdx =>
    if i < hi then
      let (out, pos, signIdx) := sampleInBallStep stream signs i out pos signIdx
      sampleInBallLoop stream signs hi fuel (i + 1) out pos signIdx
    else
      out

/-- FIPS 204 Algorithm 29. -/
def sampleInBall (p : Params) (seed : CommitHashBytes p) : Rq :=
  let stream := shake256Prefix (vectorToByteArray seed) 4096
  let signs := Id.run do
    let mut acc := 0
    for i in [0:8] do
      acc := acc + (getByteD stream i).toNat * 2 ^ (8 * i)
    return acc
  let coeffs : Array Coeff :=
    sampleInBallLoop stream signs ringDegree p.tau (ringDegree - p.tau)
      (Array.replicate ringDegree 0) 8 0
  LatticeCrypto.Poly.ofPi fun i => coeffs.getD i.val 0

/-! ## Structural output bounds for the rejection samplers

The following lemmas extract the structural value ranges of the rejection samplers from their fuel
recursion. They are the facts the abstract `Primitives.Laws` sampler-bound fields require, and are
consumed by the `concrete_*` theorems in `Extern/MLDSA/Laws.lean`. -/

open LatticeCrypto in
/-- After a `set!`, the defaulted lookup at any index is either the freshly written value or the
prior defaulted lookup. -/
private theorem getD_set!_or {α : Type*} [Inhabited α] (a : Array α) (i : ℕ) (v d : α) (j : ℕ) :
    (a.set! i v).getD j d = v ∨ (a.set! i v).getD j d = a.getD j d := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases heq : i = j <;> by_cases hj : j < a.size <;> simp [heq, hj]

/-- One `sampleInBallStep` only writes a previously stored value (`out.getD chosen 0`) and a sign
`±1`, so if every defaulted entry of `out` lies in `{0, 1, -1}` then so does every defaulted entry
of the updated accumulator. -/
private theorem sampleInBallStep_mem (stream : ByteArray) (signs i : ℕ) (out : Array Coeff)
    (pos signIdx : ℕ)
    (hInv : ∀ j, (out.getD j 0 = 0 ∨ out.getD j 0 = 1 ∨ out.getD j 0 = -1)) (j : ℕ) :
    (sampleInBallStep stream signs i out pos signIdx).1.getD j 0 = 0 ∨
      (sampleInBallStep stream signs i out pos signIdx).1.getD j 0 = 1 ∨
      (sampleInBallStep stream signs i out pos signIdx).1.getD j 0 = -1 := by
  unfold sampleInBallStep
  set chosen := (sampleInBallFindChosen stream i stream.size pos).1 with hc
  set out1 := out.set! i (out.getD chosen 0) with ho1
  set sign : Coeff := if ((signs / 2 ^ signIdx) % 2) = 0 then (1 : Coeff) else (-1 : Coeff) with hs
  have hsignPM1 : sign = 0 ∨ sign = 1 ∨ sign = -1 := by
    rw [hs]; split <;> tauto
  have hout1 : ∀ j, (out1.getD j 0 = 0 ∨ out1.getD j 0 = 1 ∨ out1.getD j 0 = -1) := by
    intro j
    rcases getD_set!_or out i (out.getD chosen 0) 0 j with h | h
    · rw [ho1, h]; exact hInv chosen
    · rw [ho1, h]; exact hInv j
  rcases getD_set!_or out1 chosen sign 0 j with h | h
  · rw [h]; exact hsignPM1
  · rw [h]; exact hout1 j

/-- The `sampleInBall` accumulator only ever holds values in `{0, 1, -1}` (every defaulted entry),
by fuel induction on the outer challenge loop, starting from the all-zero accumulator. -/
private theorem sampleInBallLoop_mem (stream : ByteArray) (signs hi : ℕ) :
    ∀ (fuel i : ℕ) (out : Array Coeff) (pos signIdx : ℕ),
      (∀ j, (out.getD j 0 = 0 ∨ out.getD j 0 = 1 ∨ out.getD j 0 = -1)) →
      ∀ j, (sampleInBallLoop stream signs hi fuel i out pos signIdx).getD j 0 = 0 ∨
        (sampleInBallLoop stream signs hi fuel i out pos signIdx).getD j 0 = 1 ∨
        (sampleInBallLoop stream signs hi fuel i out pos signIdx).getD j 0 = -1
  | 0, _, out, _, _, hInv, j => by simpa [sampleInBallLoop] using hInv j
  | fuel + 1, i, out, pos, signIdx, hInv, j => by
    unfold sampleInBallLoop
    by_cases hlt : i < hi
    · simp only [hlt, if_true]
      exact sampleInBallLoop_mem stream signs hi fuel (i + 1) _ _ _
        (fun j => sampleInBallStep_mem stream signs i out pos signIdx hInv j) j
    · simp only [hlt, if_false]
      exact hInv j

/-- Every coefficient of `sampleInBall` lies in `{0, 1, -1}`. -/
theorem sampleInBall_coeff_mem (p : Params) (seed : CommitHashBytes p) (i : Fin ringDegree) :
    (sampleInBall p seed).get i = 0 ∨ (sampleInBall p seed).get i = 1 ∨
      (sampleInBall p seed).get i = -1 := by
  unfold sampleInBall
  rw [LatticeCrypto.Poly.get_ofPi]
  apply sampleInBallLoop_mem
  intro j
  left
  rw [Array.getD_eq_getD_getElem?]
  by_cases hj : j < ringDegree <;> simp [hj]

/-- `sampleInBall` has centered infinity norm at most `1` (coefficients in `{-1, 0, +1}`). -/
theorem sampleInBall_norm (p : Params) (seed : CommitHashBytes p) :
    polyNorm (sampleInBall p seed) ≤ 1 := by
  rw [polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
  intro i
  rcases sampleInBall_coeff_mem p seed i with h | h | h <;> rw [h] <;> decide

/-! ### `ℓ₁`-norm count for `sampleInBall`

`SampleInBall` writes exactly `τ` nonzero `±1` coefficients (the outer loop runs `τ` Fisher–Yates
steps), so its centered `ℓ₁` norm — the number of nonzero coefficients — is at most `τ`. The proof
is a fuel induction tracking the nonzero count of the accumulator. Each step writes a previously
fresh diagonal slot `i` and a sign slot `chosen ≤ i`, increasing the count by exactly one; the
freshness invariant "all slots `≥ i` are zero" makes the per-step `+1` bound exact. -/

/-- The number-of-nonzero-coefficients functional on the accumulator: the `ℓ₁` norm of the
materialized polynomial equals `countNZ` of the underlying array. -/
private def countNZ (out : Array Coeff) : ℕ :=
  ∑ j ∈ Finset.range ringDegree, (LatticeCrypto.centeredRepr (out.getD j 0)).natAbs

/-- A defaulted lookup at the just-written slot returns the written value. -/
private theorem getD_set!_self (out : Array Coeff) (a : ℕ) (ha : a < out.size) (u : Coeff) :
    (out.set! a u).getD a 0 = u := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, ha, if_true,
    Option.getD_some]

/-- A defaulted lookup away from the just-written slot is unchanged. -/
private theorem getD_set!_ne (out : Array Coeff) (a : ℕ) (u : Coeff) (j : ℕ) (hj : j ≠ a) :
    (out.set! a u).getD j 0 = out.getD j 0 := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  rw [if_neg (fun h => hj h.symm)]

/-- Exact additive single-slot update law for `countNZ`, stated to avoid `ℕ` subtraction. -/
private theorem countNZ_set!_eq (out : Array Coeff) (a : ℕ) (ha : a < ringDegree)
    (hsize : out.size = ringDegree) (u : Coeff) :
    countNZ (out.set! a u) + (LatticeCrypto.centeredRepr (out.getD a 0)).natAbs
      = countNZ out + (LatticeCrypto.centeredRepr u).natAbs := by
  unfold countNZ
  have hmem : a ∈ Finset.range ringDegree := Finset.mem_range.mpr ha
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have ha' : a < out.size := by rw [hsize]; exact ha
  rw [getD_set!_self out a ha' u]
  have hrest : ∑ x ∈ (Finset.range ringDegree).erase a,
        (LatticeCrypto.centeredRepr ((out.set! a u).getD x 0)).natAbs
      = ∑ x ∈ (Finset.range ringDegree).erase a,
          (LatticeCrypto.centeredRepr (out.getD x 0)).natAbs :=
    Finset.sum_congr rfl (fun x hx => by
      rw [getD_set!_ne out a u x (Finset.ne_of_mem_erase hx)])
  rw [hrest]; ring

/-- The chosen slot index returned by the find loop is always `≤ i`. -/
private theorem findChosen_le (stream : ByteArray) (i : ℕ) :
    ∀ (fuel pos : ℕ), (sampleInBallFindChosen stream i fuel pos).1 ≤ i := by
  intro fuel
  induction fuel with
  | zero => intro pos; simp [sampleInBallFindChosen]
  | succ f ih =>
    intro pos; unfold sampleInBallFindChosen
    by_cases hb : (getByteD stream pos).toNat ≤ i
    · simp only [hb, if_true]
    · simp only [hb, if_false]; exact ih (pos + 1)

/-- One challenge step preserves the accumulator size. -/
private theorem step_size (stream : ByteArray) (signs i : ℕ) (out : Array Coeff) (pos signIdx : ℕ)
    (hsize : out.size = ringDegree) :
    (sampleInBallStep stream signs i out pos signIdx).1.size = ringDegree := by
  unfold sampleInBallStep; simp [Array.set!, hsize]

/-- One challenge step preserves the freshness invariant: slots strictly above `i` stay zero. -/
private theorem step_fresh (stream : ByteArray) (signs i : ℕ) (out : Array Coeff) (pos signIdx : ℕ)
    (hfresh : ∀ j, i ≤ j → out.getD j 0 = 0) :
    ∀ j, i + 1 ≤ j → (sampleInBallStep stream signs i out pos signIdx).1.getD j 0 = 0 := by
  intro j hj
  unfold sampleInBallStep
  set chosen := (sampleInBallFindChosen stream i stream.size pos).1 with hc
  have hchosen_le : chosen ≤ i := findChosen_le stream i stream.size pos
  rw [getD_set!_ne _ chosen _ j (by omega), getD_set!_ne _ i _ j (by omega)]
  exact hfresh j (by omega)

/-- One challenge step increases the nonzero count by at most one (in fact exactly one), given the
freshness of slot `i`. -/
private theorem step_countNZ_le (stream : ByteArray) (signs i : ℕ) (out : Array Coeff)
    (pos signIdx : ℕ) (hi : i < ringDegree) (hsize : out.size = ringDegree)
    (hfresh : (LatticeCrypto.centeredRepr (out.getD i 0)).natAbs = 0) :
    countNZ (sampleInBallStep stream signs i out pos signIdx).1 ≤ countNZ out + 1 := by
  have hchosen_le : (sampleInBallFindChosen stream i stream.size pos).1 ≤ i :=
    findChosen_le stream i stream.size pos
  unfold sampleInBallStep
  rcases hfind : sampleInBallFindChosen stream i stream.size pos with ⟨chosen, pos'⟩
  rw [hfind] at hchosen_le
  simp only at hchosen_le ⊢
  have hchosen_lt : chosen < ringDegree := lt_of_le_of_lt hchosen_le hi
  set w := out.getD chosen 0 with hw
  set out1 := out.set! i w with ho1
  set sign : Coeff := if ((signs / 2 ^ signIdx) % 2) = 0 then (1 : Coeff) else (-1 : Coeff) with hs
  have hsize1 : out1.size = ringDegree := by rw [ho1]; simp [Array.set!, hsize]
  have hsignAbs : (LatticeCrypto.centeredRepr sign).natAbs = 1 := by rw [hs]; split <;> decide
  have e1 : countNZ out1 = countNZ out + (LatticeCrypto.centeredRepr w).natAbs := by
    have := countNZ_set!_eq out i hi hsize w
    rw [hfresh, add_zero] at this; rw [ho1, this]
  have e2 := countNZ_set!_eq out1 chosen hchosen_lt hsize1 sign
  by_cases hic : chosen = i
  · have hwi : w = out.getD i 0 := by rw [hw, hic]
    have hwAbs : (LatticeCrypto.centeredRepr w).natAbs = 0 := by rw [hwi]; exact hfresh
    have hgc : out1.getD chosen 0 = w := by
      rw [hic, ho1]; exact getD_set!_self out i (by rw [hsize]; exact hi) w
    rw [hgc, hwAbs, add_zero] at e2
    rw [e2, e1, hwAbs, add_zero, hsignAbs]
  · have hgc : out1.getD chosen 0 = w := by rw [ho1]; exact getD_set!_ne out i w chosen hic
    rw [hgc] at e2; rw [e1, hsignAbs] at e2; omega

/-- The challenge loop increases the nonzero count by at most the number of indices it processes. -/
private theorem loop_countNZ_le (stream : ByteArray) (signs hi : ℕ) (hhi : hi ≤ ringDegree) :
    ∀ (fuel i : ℕ) (out : Array Coeff) (pos signIdx : ℕ),
      out.size = ringDegree → (∀ j, i ≤ j → out.getD j 0 = 0) →
      countNZ (sampleInBallLoop stream signs hi fuel i out pos signIdx) ≤ countNZ out + (hi - i)
  | 0, i, out, pos, signIdx, _, _ => by simp [sampleInBallLoop]
  | fuel + 1, i, out, pos, signIdx, hsize, hfresh => by
    unfold sampleInBallLoop
    by_cases hlt : i < hi
    · simp only [hlt, if_true]
      set stepOut := (sampleInBallStep stream signs i out pos signIdx) with hstep
      have hi' : i < ringDegree := lt_of_lt_of_le hlt hhi
      have hfreshi : (LatticeCrypto.centeredRepr (out.getD i 0)).natAbs = 0 := by
        rw [hfresh i (le_refl i)]; decide
      have hstepsize : stepOut.1.size = ringDegree := step_size stream signs i out pos signIdx hsize
      have hstepfresh : ∀ j, i + 1 ≤ j → stepOut.1.getD j 0 = 0 :=
        step_fresh stream signs i out pos signIdx hfresh
      have hcount : countNZ stepOut.1 ≤ countNZ out + 1 :=
        step_countNZ_le stream signs i out pos signIdx hi' hsize hfreshi
      have ih := loop_countNZ_le stream signs hi hhi fuel (i + 1) stepOut.1 stepOut.2.1 stepOut.2.2
        hstepsize hstepfresh
      calc countNZ (sampleInBallLoop stream signs hi fuel (i + 1)
            stepOut.1 stepOut.2.1 stepOut.2.2)
          ≤ countNZ stepOut.1 + (hi - (i + 1)) := ih
        _ ≤ (countNZ out + 1) + (hi - (i + 1)) := by omega
        _ = countNZ out + (hi - i) := by omega
    · simp only [hlt, if_false]
      exact Nat.le_add_right _ _

/-- The all-zero accumulator has nonzero count zero. -/
private theorem countNZ_replicate_zero : countNZ (Array.replicate ringDegree (0 : Coeff)) = 0 := by
  unfold countNZ
  apply Finset.sum_eq_zero
  intro j _
  rw [Array.getD_eq_getD_getElem?]
  simp only [Array.getElem?_replicate]
  by_cases h : j < ringDegree <;> simp only [h, if_true, if_false, Option.getD] <;> decide

/-- The `ℓ₁` norm of a polynomial materialized by `Vector.ofFn` from a defaulted-array lookup is the
nonzero count of that array. -/
private theorem l1Norm_ofPi_eq_countNZ (coeffs : Array Coeff) :
    LatticeCrypto.l1Norm (LatticeCrypto.Poly.ofPi
      (fun i : Fin ringDegree => coeffs.getD i.val 0))
      = countNZ coeffs := by
  rw [LatticeCrypto.l1Norm_eq_sum]
  unfold countNZ
  rw [Finset.sum_range (fun j => (LatticeCrypto.centeredRepr (coeffs.getD j 0)).natAbs)]
  apply Finset.sum_congr rfl
  intro i _
  rw [LatticeCrypto.Poly.get_ofPi]

/-- The challenge loop, run from the all-zero accumulator over `[ringDegree - τ, ringDegree)`,
produces an array with nonzero count at most `τ`. -/
private theorem countNZ_sampleInBallLoop_le (stream : ByteArray) (signs : ℕ) (p : Params) :
    countNZ (sampleInBallLoop stream signs ringDegree p.tau (ringDegree - p.tau)
      (Array.replicate ringDegree 0) 8 0) ≤ p.tau := by
  have hsize : (Array.replicate ringDegree (0 : Coeff)).size = ringDegree :=
    Array.size_replicate
  have hfresh : ∀ j, ringDegree - p.tau ≤ j →
      (Array.replicate ringDegree (0 : Coeff)).getD j 0 = 0 := by
    intro j _
    rw [Array.getD_eq_getD_getElem?]; simp only [Array.getElem?_replicate]
    by_cases h : j < ringDegree <;> simp only [h, if_true, if_false, Option.getD]
  have hloop := loop_countNZ_le stream signs ringDegree (le_refl _) p.tau (ringDegree - p.tau)
    (Array.replicate ringDegree 0) 8 0 hsize hfresh
  rw [countNZ_replicate_zero, zero_add] at hloop
  exact le_trans hloop (by omega)

/-- `sampleInBall` has centered `ℓ₁` norm at most `τ` (it writes at most `τ` nonzero `±1`
coefficients). This is the count needed for the challenge-product bound `‖c · s‖∞ ≤ τ · η`. -/
theorem sampleInBall_l1Norm (p : Params) (seed : CommitHashBytes p) :
    LatticeCrypto.l1Norm (sampleInBall p seed) ≤ p.tau := by
  unfold sampleInBall
  rw [l1Norm_ofPi_eq_countNZ]
  exact countNZ_sampleInBallLoop_le _ _ p

/-- After a `push`, the defaulted lookup at any index is either the pushed value or the prior
defaulted lookup. -/
private theorem getD_push_or {α : Type*} [Inhabited α] (a : Array α) (v d : α) (j : ℕ) :
    (a.push v).getD j d = v ∨ (a.push v).getD j d = a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : j < a.size <;> by_cases h2 : j = a.size <;> simp [h, h2]

/-- Predicate: casting every defaulted entry of an integer array into `Coeff` yields a centered
representative of absolute value at most `eta`. Working at the `Coeff` level here sidesteps any
`2 * eta < modulus` side condition: in the inactive `eta ∉ {2, 4}` case the array stays all-zero and
the cast of `0` has centered representative `0`. -/
private def EtaInv (eta : ℕ) (c : Array ℤ) : Prop :=
  ∀ j, (LatticeCrypto.centeredRepr (((c.getD j 0 : ℤ) : Coeff))).natAbs ≤ eta

/-- A conditional push of a value whose `Coeff` cast is centered-bounded by `eta` (whenever the
guard holds) preserves `EtaInv`. -/
private theorem EtaInv_condPush (eta : ℕ) (c : Array ℤ) (v : ℤ) (cond : Prop) [Decidable cond]
    (hc : EtaInv eta c)
    (hv : cond → (LatticeCrypto.centeredRepr ((v : Coeff))).natAbs ≤ eta) :
    EtaInv eta (if cond then c.push v else c) := by
  intro j
  split
  · rename_i hcond
    rcases getD_push_or c v 0 j with h | h
    · rw [h]; exact hv hcond
    · rw [h]; exact hc j
  · exact hc j

/-- One `rejEtaStep` only pushes values whose `Coeff` cast is centered-bounded by `eta` (in the
`eta = 2` and `eta = 4` branches; in any other case it pushes nothing). So `EtaInv eta` is preserved
by a step. -/
private theorem rejEtaStep_mem (eta byte : ℕ) (coeffs : Array ℤ)
    (hInv : EtaInv eta coeffs) : EtaInv eta (rejEtaStep eta byte coeffs) := by
  unfold rejEtaStep
  have hb2 : ∀ (tt : ℕ), tt < 15 →
      (LatticeCrypto.centeredRepr
        ((((2 : ℤ) - ((tt - (Nat.shiftRight (205 * tt) 10) * 5 : ℕ) : ℤ)) : ℤ) : Coeff)).natAbs ≤ 2
        := by decide
  have hb4 : ∀ (tt : ℕ), tt < 9 →
      (LatticeCrypto.centeredRepr ((((4 : ℤ) - (tt : ℤ)) : ℤ) : Coeff)).natAbs ≤ 4 := by decide
  set t0 := byte &&& 0x0F
  set t1 := Nat.shiftRight byte 4
  split
  · -- eta = 2
    rename_i he2; subst he2
    refine EtaInv_condPush 2 _ _ _ (EtaInv_condPush 2 _ _ _ hInv ?_) ?_
    · exact fun hcond => hb2 t0 hcond.1
    · exact fun hcond => hb2 t1 hcond.1
  · split
    · rename_i he4; subst he4
      refine EtaInv_condPush 4 _ _ _ (EtaInv_condPush 4 _ _ _ hInv ?_) ?_
      · exact fun hcond => hb4 t0 hcond.1
      · exact fun hcond => hb4 t1 hcond.1
    · exact hInv

/-- `EtaInv eta` is preserved through the whole `rejEtaCoeffsAux` fuel recursion. -/
private theorem rejEtaCoeffsAux_mem (eta : ℕ) (stream : ByteArray) :
    ∀ (fuel : ℕ) (coeffs : Array ℤ) (pos : ℕ),
      EtaInv eta coeffs → EtaInv eta (rejEtaCoeffsAux eta stream fuel coeffs pos)
  | 0, coeffs, _, hInv => by simpa [rejEtaCoeffsAux] using hInv
  | fuel + 1, coeffs, pos, hInv => by
    unfold rejEtaCoeffsAux
    by_cases h : coeffs.size < ringDegree ∧ pos < stream.size
    · simp only [h]
      exact rejEtaCoeffsAux_mem eta stream fuel _ _ (rejEtaStep_mem eta _ coeffs hInv)
    · simp only [h, ite_false]
      exact hInv

/-- The centered representative of the `Coeff` cast of `0` has absolute value `0`. -/
private theorem centeredRepr_zero_cast_le (eta : ℕ) :
    (LatticeCrypto.centeredRepr (((0 : ℤ) : Coeff))).natAbs ≤ eta := by
  have : LatticeCrypto.centeredRepr (((0 : ℤ) : Coeff)) = 0 := by decide
  rw [this]; exact Nat.zero_le eta

private theorem EtaInv_mkEmpty (eta : ℕ) : EtaInv eta (Array.mkEmpty ringDegree) := by
  intro j
  have hz : (Array.mkEmpty ringDegree : Array ℤ).getD j 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?]; simp
  rw [hz]
  exact centeredRepr_zero_cast_le eta

/-- The `requireFullEtaSample` guard preserves `EtaInv`: it returns either the input array or the
empty fallback, both `EtaInv`. -/
private theorem requireFullEtaSample_mem (eta : ℕ) (coeffs : Array ℤ) (hInv : EtaInv eta coeffs) :
    EtaInv eta (requireFullEtaSample coeffs) := by
  unfold requireFullEtaSample
  split
  · exact hInv
  · -- `panic!` reduces to the `Inhabited` default for `Array ℤ`, the empty array (size `0`), so
    -- every defaulted lookup is `0`.
    intro j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.mpr (Nat.zero_le j),
      Option.getD_none]
    exact centeredRepr_zero_cast_le eta

/-- Every coefficient of `sampleEtaPoly eta seed nonce` has centered infinity norm at most `eta`. -/
theorem sampleEtaPoly_norm (eta : ℕ) (seed : Bytes 64) (nonce : ℕ) :
    polyNorm (sampleEtaPoly eta seed nonce) ≤ eta := by
  rw [polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
  intro i
  unfold sampleEtaPoly
  simp only [Vector.get_ofFn]
  exact requireFullEtaSample_mem eta _ (rejEtaCoeffsAux_mem eta _ _ _ _ (EtaInv_mkEmpty eta)) i.val

/-- `expandS` produces secret vectors with every coefficient bounded by `η`. -/
theorem expandS_bound (rhoPrime : Bytes 64) (p : Params) :
    polyVecBounded (expandS rhoPrime p).1 p.eta ∧
      polyVecBounded (expandS rhoPrime p).2 p.eta := by
  constructor <;>
  · rw [polyVecBounded, polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff]
    intro j
    unfold expandS
    simp only [Vector.get_ofFn]
    exact sampleEtaPoly_norm p.eta rhoPrime _

/-! ## Hash wrappers -/

/-- Hash the transcript and message into the 64-byte `μ` value used by ML-DSA. -/
def hashMessage (tr : Bytes 64) (msg : List Byte) : Bytes 64 :=
  hashBytes64 (vectorToByteArray tr ++ ByteArray.mk msg.toArray)

/-- Hash the secret key material and `μ` into the seed used during signing. -/
def hashPrivateSeed (key rnd : Bytes 32) (mu : Bytes 64) : Bytes 64 :=
  hashBytes64 (vectorToByteArray key ++ vectorToByteArray rnd ++ vectorToByteArray mu)

/-- Hash `μ` and the encoded `w₁` bytes into the challenge seed `c̃`. -/
def hashCommitmentBytes (mu : Bytes 64) (w1 : ByteArray) (p : Params) : CommitHashBytes p :=
  shake256Vector (vectorToByteArray mu ++ w1) (p.lambda / 4)

/-- Hash an encoded public key into the transcript prefix `tr`. -/
def hashPublicKeyBytes (pkBytes : ByteArray) : Bytes 64 :=
  hashBytes64 pkBytes

end MLDSA.Concrete
