/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Batteries.Data.Float.Rat
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Exp
public import LatticeCrypto.Falcon.Primitives
public import LatticeCrypto.Falcon.Concrete.FloatLike
public import LatticeCrypto.Falcon.Concrete.NTT
public import LatticeCrypto.Falcon.Concrete.Encoding
public import LatticeCrypto.Falcon.Concrete.FXR
public import Extern.Falcon.SamplerZ
public import Extern.Falcon.Sampling
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Concrete Falcon Instance

Wires the concrete NTT, encoding, and sampling modules into the abstract
`Primitives` bundle, and provides a standalone executable `concreteVerify`
function for testing.

## Two-Track Design

1. **`concreteVerify`**: Standalone executable function wiring concrete modules
   directly. Does not go through the abstract `Primitives` structure. This is
   the testable surface.

2. **`concretePrimitives`**: Fills the abstract `Primitives` structure with
   concrete implementations for the executable fields and a concrete FXR-backed
   bridge for the FFT conversion fields. Used to connect the proof-level Falcon
   interface to the concrete packed FFT representation.

## Kernel correctness

The fast `UInt32`/`Int64` kernels used by `concreteVerify` compute exactly their
specification-level counterparts: `negacyclicMulU32_eq_negacyclicMul` at every degree, and
`pairL2NormSqU32_eq_pairL2NormSq` under the `UInt64` no-overflow bound
`2 · n · (q/2)² < 2⁶⁴`, which holds with vast headroom for every Falcon degree.
-/

public section


namespace Falcon.Concrete

open Falcon

/-! ## Standalone executable verify -/

/-- Fast negacyclic multiplication using `UInt32` arithmetic, avoiding Mathlib's
`ZMod` typeclass dispatch and heap allocation overhead. Computes the same result
as `negacyclicMul` but ~1000× faster for `q = 12289`. -/
def negacyclicMulU32 {n : ℕ} (f g : Rq n) : Rq n := Id.run do
  let q : UInt32 := modulus.toUInt32
  let fa := f.toArray.map (fun c => (ZMod.val c).toUInt32)
  let ga := g.toArray.map (fun c => (ZMod.val c).toUInt32)
  let mut out : Array UInt32 := Array.replicate n 0
  for i in [0:n] do
    let fi := fa.getD i 0
    for j in [0:n] do
      let gj := ga.getD j 0
      let prod := fi * gj % q
      let k := (i + j) % n
      let cur := out.getD k 0
      if i + j < n then
        let s := cur + prod
        out := out.set! k (if s >= q then s - q else s)
      else
        out := out.set! k (if cur >= prod then cur - prod else cur + q - prod)
  return Vector.ofFn fun ⟨i, _⟩ => (Nat.cast (out.getD i 0).toNat : ZMod modulus)

/-- Fast squared ℓ₂ norm of a pair of polynomials using `Int32`/`UInt64`
arithmetic, avoiding `ℤ` and `Finset.sum` overhead. -/
def pairL2NormSqU32 {n : ℕ} (s₁ s₂ : Rq n) : Nat := Id.run do
  let q : Int64 := modulus.toUInt64.toInt64
  let halfQ : UInt32 := (modulus / 2).toUInt32
  let mut sqn : UInt64 := 0
  for i in [0:n] do
    let v := (ZMod.val (s₁.getD i 0)).toUInt32
    let c : Int64 := if v ≤ halfQ then v.toUInt64.toInt64 else v.toUInt64.toInt64 - q
    sqn := sqn + (c * c).toUInt64
  for i in [0:n] do
    let v := (ZMod.val (s₂.getD i 0)).toUInt32
    let c : Int64 := if v ≤ halfQ then v.toUInt64.toInt64 else v.toUInt64.toInt64 - q
    sqn := sqn + (c * c).toUInt64
  return sqn.toNat

/-- Standalone executable Falcon verification using the concrete hash, codec, and arithmetic
implementations. -/
def concreteVerify (p : Params) (pk : ByteArray) (msg : List Byte)
    (sig : ByteArray) : Bool := Id.run do
  let logn := p.logn
  match sigDecode sig logn with
  | none => return false
  | some (salt, compSig) =>
    match decompress p.n compSig p.sbytelen with
    | none => return false
    | some s2Int =>
      match pkDecode p.n (pk.extract 1 pk.size) with
      | none => return false
      | some h =>
        let c := hashToPoint p.n salt pk msg
        let s2 := IntPoly.toRq s2Int
        let s1 := c - negacyclicMulU32 s2 h
        return pairL2NormSqU32 s1 s2 ≤ p.betaSquared

@[simp] theorem concreteVerify_sigEncode_nil_eq_false
    (p : Params) (pk : ByteArray) (salt : Bytes 40) (msg : List Byte) :
    concreteVerify p pk msg (sigEncode salt [] p.logn) = false := by
  simp [concreteVerify]

/-! ## Kernel correctness

The standalone executable verifier `concreteVerify` uses the `UInt32`/`Int64`
fast kernels `negacyclicMulU32` and `pairL2NormSqU32`. These theorems certify
that the fast kernels compute exactly the abstract specification-level
`negacyclicMul` and `pairL2NormSq`, discharging the `hmul`/`hnorm` hypotheses of
`Falcon.Concrete.FPRBridge.concrete_verify_eq_verify`. -/

/-! ### Negacyclic multiplier correctness

The `negacyclicMulU32` kernel folds an imperative `O(n²)` double loop over a
`UInt32` accumulator array. The helpers below characterize that loop by a
`Finset`-sum invariant in `ZMod modulus` and bridge it to the
specification-level coefficient `LatticeCrypto.negacyclicConvCoeff`. Each output
cell stays in `[0, modulus)` for every degree, so no degree bound is required. -/
private theorem q_toNat : (modulus.toUInt32).toNat = 12289 := by
  change (UInt32.ofNat modulus).toNat = 12289
  rw [UInt32.toNat_ofNat']; rfl

private theorem cast_natSub {a b : ℕ} (h : b ≤ a) :
    ((a - b : ℕ) : ZMod modulus) = (a : ZMod modulus) - (b : ZMod modulus) := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_add, Nat.sub_add_cancel h]

private theorem prodU32 (a b : UInt32) (ha : a.toNat < modulus) (hb : b.toNat < modulus) :
    (a * b % modulus.toUInt32).toNat < modulus ∧
      ((a * b % modulus.toUInt32).toNat : ZMod modulus)
        = (a.toNat : ZMod modulus) * (b.toNat : ZMod modulus) := by
  have hq : (modulus.toUInt32).toNat = 12289 := q_toNat
  have hmul : (a * b).toNat = a.toNat * b.toNat := by
    rw [UInt32.toNat_mul, Nat.mod_eq_of_lt]
    have hlt : a.toNat * b.toNat < 12289 * 12289 := by
      apply Nat.mul_lt_mul'' <;> simpa [modulus] using ‹_›
    calc a.toNat * b.toNat < 12289 * 12289 := hlt
      _ < 2^32 := by norm_num
  have hmod : (a * b % modulus.toUInt32).toNat = (a.toNat * b.toNat) % 12289 := by
    rw [UInt32.toNat_mod, hmul, hq]
  refine ⟨?_, ?_⟩
  · rw [hmod]; simpa [modulus] using Nat.mod_lt _ (by norm_num)
  · rw [hmod, show (12289 : ℕ) = modulus from rfl]
    push_cast [ZMod.natCast_mod, Nat.cast_mul]; ring

private theorem addCellU32 (cur prod : UInt32) (hc : cur.toNat < modulus)
    (hp : prod.toNat < modulus) :
    (if cur + prod ≥ modulus.toUInt32 then cur + prod - modulus.toUInt32 else cur + prod).toNat
        < modulus
    ∧ ((if cur + prod ≥ modulus.toUInt32 then cur + prod - modulus.toUInt32 else cur + prod).toNat
        : ZMod modulus) = (cur.toNat : ZMod modulus) + (prod.toNat : ZMod modulus) := by
  have hq : (modulus.toUInt32).toNat = 12289 := q_toNat
  have hmm : (modulus : ℕ) = 12289 := rfl
  have hpow : (2:ℕ)^32 = 4294967296 := by norm_num
  rw [hmm] at hc hp
  have hadd : (cur + prod).toNat = cur.toNat + prod.toNat := by
    rw [UInt32.toNat_add, hpow, Nat.mod_eq_of_lt]; omega
  simp only [ge_iff_le, UInt32.le_iff_toNat_le, hq, hadd]
  by_cases h : 12289 ≤ cur.toNat + prod.toNat
  · rw [if_pos h]
    have hsub : (cur + prod - modulus.toUInt32).toNat = cur.toNat + prod.toNat - 12289 := by
      rw [UInt32.toNat_sub, hq, hadd, hpow]; omega
    rw [hsub]
    refine ⟨by rw [hmm]; omega, ?_⟩
    rw [cast_natSub h]; push_cast
    rw [show (12289 : ZMod modulus) = ((modulus:ℕ):ZMod modulus) from rfl, ZMod.natCast_self]; ring
  · rw [if_neg h, hadd]
    exact ⟨by rw [hmm]; omega, by push_cast; ring⟩

private theorem subCellU32 (cur prod : UInt32) (hc : cur.toNat < modulus)
    (hp : prod.toNat < modulus) :
    (if cur ≥ prod then cur - prod else cur + modulus.toUInt32 - prod).toNat < modulus
    ∧ ((if cur ≥ prod then cur - prod else cur + modulus.toUInt32 - prod).toNat : ZMod modulus)
        = (cur.toNat : ZMod modulus) - (prod.toNat : ZMod modulus) := by
  have hq : (modulus.toUInt32).toNat = 12289 := q_toNat
  have hmm : (modulus : ℕ) = 12289 := rfl
  have hpow : (2:ℕ)^32 = 4294967296 := by norm_num
  rw [hmm] at hc hp
  simp only [ge_iff_le, UInt32.le_iff_toNat_le]
  by_cases h : prod.toNat ≤ cur.toNat
  · rw [if_pos h]
    have hsub : (cur - prod).toNat = cur.toNat - prod.toNat := by rw [UInt32.toNat_sub, hpow]; omega
    rw [hsub]; exact ⟨by rw [hmm]; omega, by rw [cast_natSub h]⟩
  · rw [if_neg h]
    have hcadd : (cur + modulus.toUInt32).toNat = cur.toNat + 12289 := by
      rw [UInt32.toNat_add, hq, hpow]; omega
    have hsub : (cur + modulus.toUInt32 - prod).toNat = cur.toNat + 12289 - prod.toNat := by
      rw [UInt32.toNat_sub, hcadd, hpow]; omega
    rw [hsub]
    refine ⟨by rw [hmm]; omega, ?_⟩
    rw [cast_natSub (by omega : prod.toNat ≤ cur.toNat + 12289)]
    push_cast
    rw [show (12289 : ZMod modulus) = ((modulus:ℕ):ZMod modulus) from rfl, ZMod.natCast_self]; ring

private def innerStep {n : ℕ} (fa ga : Array UInt32) (i : ℕ) (r : Array UInt32) (j : ℕ) :
    Array UInt32 :=
  let prod := fa.getD i 0 * ga.getD j 0 % modulus.toUInt32
  let kk := (i + j) % n
  let cur := r.getD kk 0
  if i + j < n then r.set! kk (if cur + prod ≥ modulus.toUInt32 then cur + prod - modulus.toUInt32
                                else cur + prod)
  else r.set! kk (if cur ≥ prod then cur - prod else cur + modulus.toUInt32 - prod)

private theorem getD_set!_self (out : Array UInt32) (k : ℕ) (v : UInt32) (h : k < out.size) :
    (out.set! k v).getD k 0 = v := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]; simp [h]

private theorem getD_set!_ne (out : Array UInt32) (k k' : ℕ) (v : UInt32) (h : k ≠ k') :
    (out.set! k v).getD k' 0 = out.getD k' 0 := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]; simp [h]

private theorem foldl_range_succ {α} (fn : α → ℕ → α) (x : α) (m : ℕ) :
    List.foldl fn x (List.range (m+1)) = fn (List.foldl fn x (List.range m)) m := by
  rw [List.range_succ, List.foldl_append]; simp

-- innerStep preserves size

private theorem innerStep_size {n : ℕ} (fa ga : Array UInt32) (i : ℕ) (r : Array UInt32) (j : ℕ) :
    (@innerStep n fa ga i r j).size = r.size := by
  unfold innerStep
  split <;> simp

-- the per-cell summand value (in ZMod) for column j landing

private def colVal (n : ℕ) (fa ga : Array UInt32) (i j : ℕ) : ZMod modulus :=
  if i + j < n then ((fa.getD i 0).toNat : ZMod modulus) * ((ga.getD j 0).toNat : ZMod modulus)
  else -(((fa.getD i 0).toNat : ZMod modulus) * ((ga.getD j 0).toNat : ZMod modulus))

-- inner loop invariant: by induction on J

private theorem inner_invariant {n : ℕ} (fa ga : Array UInt32) (i : ℕ) (hi : i < n)
    (hfi : (fa.getD i 0).toNat < modulus) (hgaB : ∀ j, (ga.getD j 0).toNat < modulus)
    (r0 : Array UInt32) (hsz0 : r0.size = n)
    (hb0 : ∀ k, k < n → (r0.getD k 0).toNat < modulus) :
    ∀ J, J ≤ n →
      (List.foldl (fun r j => @innerStep n fa ga i r j) r0 (List.range J)).size = n ∧
      (∀ k, k < n →
        ((List.foldl (fun r j => @innerStep n fa ga i r j) r0 (List.range J)).getD k 0).toNat
          < modulus) ∧
      (∀ k, k < n →
        (((List.foldl (fun r j => @innerStep n fa ga i r j) r0 (List.range J)).getD k 0).toNat
            : ZMod modulus)
          = ((r0.getD k 0).toNat : ZMod modulus)
            + ∑ j ∈ (Finset.range J).filter (fun j => (i + j) % n = k), colVal n fa ga i j) := by
  intro J
  induction J with
  | zero =>
    intro _
    refine ⟨hsz0, ?_, ?_⟩
    · simpa using hb0
    · intro k hk; simp
  | succ J ih =>
    intro hJ
    have hJ' : J ≤ n := Nat.le_of_succ_le hJ
    obtain ⟨ihsz, ihb, ihv⟩ := ih hJ'
    set r := List.foldl (fun r j => @innerStep n fa ga i r j) r0 (List.range J) with hr
    rw [foldl_range_succ]
    -- the new array
    set r' := @innerStep n fa ga i r J with hr'
    have hJn : J < n := Nat.lt_of_succ_le hJ
    have hkk : (i + J) % n < n := Nat.mod_lt _ (by omega)
    have hprod := prodU32 (fa.getD i 0) (ga.getD J 0) hfi (hgaB J)
    -- size of r'
    have hszr' : r'.size = n := by rw [hr', innerStep_size, ihsz]
    refine ⟨hszr', ?_, ?_⟩
    · -- bound
      intro k hk
      by_cases hkeq : (i + J) % n = k
      · subst hkeq
        rw [hr']
        unfold innerStep
        by_cases hlt : i + J < n
        · rw [if_pos hlt, getD_set!_self _ _ _ (by rw [ihsz]; exact hkk)]
          exact (addCellU32 (r.getD ((i+J)%n) 0) _ (ihb _ hkk) hprod.1).1
        · rw [if_neg hlt, getD_set!_self _ _ _ (by rw [ihsz]; exact hkk)]
          exact (subCellU32 (r.getD ((i+J)%n) 0) _ (ihb _ hkk) hprod.1).1
      · rw [hr']
        unfold innerStep
        rw [show (if i + J < n then r.set! ((i+J)%n) _ else r.set! ((i+J)%n) _)
              = r.set! ((i+J)%n) (if i + J < n then _ else _) from by split <;> rfl]
        rw [getD_set!_ne _ _ _ _ hkeq]
        exact ihb k hk
    · -- value
      intro k hk
      have hfilt : (Finset.range (J+1)).filter (fun j => (i + j) % n = k)
          = if (i + J) % n = k then insert J ((Finset.range J).filter (fun j => (i + j) % n = k))
            else (Finset.range J).filter (fun j => (i + j) % n = k) := by
        rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hkeq : (i + J) % n = k
      · subst hkeq
        rw [hr']
        unfold innerStep
        have hJnotmem : J ∉ (Finset.range J).filter (fun j => (i + j) % n = (i + J) % n) := by
          simp
        rw [hfilt, if_pos rfl, Finset.sum_insert hJnotmem]
        by_cases hlt : i + J < n
        · rw [if_pos hlt, getD_set!_self _ _ _ (by rw [ihsz]; exact hkk)]
          rw [(addCellU32 (r.getD ((i+J)%n) 0) _ (ihb _ hkk) hprod.1).2]
          rw [ihv _ hkk, hprod.2]
          unfold colVal
          rw [if_pos hlt]; ring
        · rw [if_neg hlt, getD_set!_self _ _ _ (by rw [ihsz]; exact hkk)]
          rw [(subCellU32 (r.getD ((i+J)%n) 0) _ (ihb _ hkk) hprod.1).2]
          rw [ihv _ hkk, hprod.2]
          unfold colVal
          rw [if_neg hlt]; ring
      · rw [hfilt, if_neg hkeq]
        rw [hr']
        unfold innerStep
        rw [show (if i + J < n then r.set! ((i+J)%n) _ else r.set! ((i+J)%n) _)
              = r.set! ((i+J)%n) (if i + J < n then _ else _) from by split <;> rfl]
        rw [getD_set!_ne _ _ _ _ hkeq]
        exact ihv k hk

private def outerStep {n : ℕ} (fa ga : Array UInt32) (r : Array UInt32) (i : ℕ) :
    Array UInt32 :=
  List.foldl (fun r j => @innerStep n fa ga i r j) r (List.range n)

-- outerStep effect: specialize inner_invariant to J = n

private theorem outerStep_spec {n : ℕ} (fa ga : Array UInt32) (i : ℕ) (hi : i < n)
    (hfi : (fa.getD i 0).toNat < modulus) (hgaB : ∀ j, (ga.getD j 0).toNat < modulus)
    (r0 : Array UInt32) (hsz0 : r0.size = n)
    (hb0 : ∀ k, k < n → (r0.getD k 0).toNat < modulus) :
    (@outerStep n fa ga r0 i).size = n ∧
    (∀ k, k < n → ((@outerStep n fa ga r0 i).getD k 0).toNat < modulus) ∧
    (∀ k, k < n →
      (((@outerStep n fa ga r0 i).getD k 0).toNat : ZMod modulus)
        = ((r0.getD k 0).toNat : ZMod modulus)
          + ∑ j ∈ (Finset.range n).filter (fun j => (i + j) % n = k), colVal n fa ga i j) := by
  have := inner_invariant fa ga i hi hfi hgaB r0 hsz0 hb0 n (le_refl n)
  exact this

-- outer invariant: by induction on I

private theorem outer_invariant {n : ℕ} (fa ga : Array UInt32)
    (hfaB : ∀ i, i < n → (fa.getD i 0).toNat < modulus)
    (hgaB : ∀ j, (ga.getD j 0).toNat < modulus) :
    ∀ I, I ≤ n →
      (List.foldl (fun r i => @outerStep n fa ga r i) (Array.replicate n 0) (List.range I)).size = n
      ∧ (∀ k, k < n →
          ((List.foldl (fun r i => @outerStep n fa ga r i)
            (Array.replicate n 0) (List.range I)).getD k 0).toNat < modulus)
      ∧ (∀ k, k < n →
          (((List.foldl (fun r i => @outerStep n fa ga r i)
            (Array.replicate n 0) (List.range I)).getD k 0).toNat : ZMod modulus)
            = ∑ ij ∈ (Finset.range I ×ˢ Finset.range n).filter (fun ij => (ij.1 + ij.2) % n = k),
                colVal n fa ga ij.1 ij.2) := by
  intro I
  induction I with
  | zero =>
    intro _
    have hrep0 : ∀ k, k < n → (Array.replicate n (0:UInt32)).getD k 0 = 0 := by
      intro k hk
      rw [Array.getD, dif_pos (by rw [Array.size_replicate]; exact hk)]; simp
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨by simp, ?_, ?_⟩
    · intro k hk; rw [hrep0 k hk]; simp [modulus]
    · intro k hk
      simp only [Finset.range_zero, Finset.empty_product, Finset.filter_empty,
        Finset.sum_empty]
      rw [hrep0 k hk]; simp
  | succ I ih =>
    intro hI
    have hI' : I ≤ n := Nat.le_of_succ_le hI
    have hIn : I < n := Nat.lt_of_succ_le hI
    obtain ⟨ihsz, ihb, ihv⟩ := ih hI'
    set r := List.foldl (fun r i => @outerStep n fa ga r i)
      (Array.replicate n 0) (List.range I) with hr
    rw [foldl_range_succ]
    obtain ⟨ospz, ospb, ospv⟩ :=
      outerStep_spec fa ga I hIn (hfaB I hIn) hgaB r ihsz ihb
    refine ⟨ospz, ospb, ?_⟩
    intro k hk
    rw [ospv k hk, ihv k hk]
    -- split the product index set range (I+1) ×ˢ range n into range I and row {I}
    have hsplit : (Finset.range (I+1) ×ˢ Finset.range n).filter (fun ij => (ij.1 + ij.2) % n = k)
        = ((Finset.range I ×ˢ Finset.range n).filter (fun ij => (ij.1 + ij.2) % n = k))
          ∪ (({I} ×ˢ Finset.range n).filter (fun ij => (ij.1 + ij.2) % n = k)) := by
      ext ij
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_union,
        Finset.mem_singleton, Finset.range_add_one, Finset.mem_insert]
      constructor
      · rintro ⟨⟨h1 | h1, h2⟩, h3⟩
        · exact Or.inr ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨Or.inr h1, h2⟩, h3⟩
        · exact ⟨⟨Or.inl h1, h2⟩, h3⟩
    rw [hsplit, Finset.sum_union]
    · congr 1
      -- second sum over {I} ×ˢ range n filtered = ∑ j ∈ (range n).filter, colVal
      rw [Finset.singleton_product, Finset.filter_map, Finset.sum_map]
      apply Finset.sum_congr
      · ext j; simp
      · intro j hj; rfl
    · -- disjointness
      rw [Finset.disjoint_left]
      rintro ij hij1 hij2
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_singleton] at hij1 hij2
      omega

private theorem mulU32_eq_foldl {n : ℕ} (f g : Rq n) :
    negacyclicMulU32 f g
      = Vector.ofFn (fun x : Fin n =>
          (Nat.cast ((List.foldl
            (fun r i => @outerStep n (f.toArray.map (fun c => (ZMod.val c).toUInt32))
                  (g.toArray.map (fun c => (ZMod.val c).toUInt32)) r i)
              (Array.replicate n 0) (List.range n)).getD x.val 0).toNat : ZMod modulus)) := by
  unfold negacyclicMulU32 outerStep innerStep
  simp only [Id.run, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one, List.range_eq_range', Nat.add_sub_cancel]
  simp only [← apply_ite (f := fun a => pure (f := Id) (ForInStep.yield a))]
  simp only [List.forIn_pure_yield_eq_foldl, map_pure]
  rfl

private theorem fa_getD {n : ℕ} (f : Rq n) (i : ℕ) (hi : i < n) :
    (f.toArray.map (fun c => (ZMod.val c).toUInt32)).getD i 0
      = (ZMod.val (f.get ⟨i, hi⟩)).toUInt32 := by
  have hsz : i < (f.toArray.map (fun c => (ZMod.val c).toUInt32)).size := by
    rw [Array.size_map, f.size_toArray]; exact hi
  rw [← Array.getElem_eq_getD (xs := f.toArray.map (fun c => (ZMod.val c).toUInt32))
      (i := i) (fallback := 0) (h := hsz), Array.getElem_map]
  rfl

private theorem fa_cast {n : ℕ} (f : Rq n) (i : ℕ) (hi : i < n) :
    (((f.toArray.map (fun c => (ZMod.val c).toUInt32)).getD i 0).toNat : ZMod modulus)
      = f.get ⟨i, hi⟩ := by
  rw [fa_getD f i hi]
  have : (ZMod.val (f.get ⟨i, hi⟩)).toUInt32.toNat = ZMod.val (f.get ⟨i, hi⟩) := by
    have hval : ZMod.val (f.get ⟨i,hi⟩) < 12289 := ZMod.val_lt _
    change (UInt32.ofNat _).toNat = _
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [this, ZMod.natCast_zmod_val]

private theorem fa_bound {n : ℕ} (f : Rq n) (i : ℕ) (hi : i < n) :
    ((f.toArray.map (fun c => (ZMod.val c).toUInt32)).getD i 0).toNat < modulus := by
  rw [fa_getD f i hi]
  have hval : ZMod.val (f.get ⟨i,hi⟩) < 12289 := ZMod.val_lt _
  change (UInt32.ofNat _).toNat < _
  rw [UInt32.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega)]; exact hval

/-- The `UInt32` fast negacyclic multiplier agrees with the abstract `negacyclicMul`. -/
theorem negacyclicMulU32_eq_negacyclicMul {n : ℕ} (f g : Rq n) :
    negacyclicMulU32 f g = Falcon.negacyclicMul f g := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro k
  -- RHS coefficient
  have hrhs : (Falcon.negacyclicMul f g).get k
      = LatticeCrypto.negacyclicConvCoeff (fun i => f.get i) (fun i => g.get i) k := by
    change ((LatticeCrypto.vectorNegacyclicRing Coeff n).mul f g).get k = _
    rw [LatticeCrypto.vectorNegacyclicRing_mul]
    exact LatticeCrypto.negacyclicMulPure_coeff (LatticeCrypto.vectorKernel Coeff n) f g k
  rw [hrhs]
  -- LHS coefficient
  rw [mulU32_eq_foldl]
  simp only [Vector.get_ofFn]
  set fa := f.toArray.map (fun c => (ZMod.val c).toUInt32) with hfa
  set ga := g.toArray.map (fun c => (ZMod.val c).toUInt32) with hga
  obtain ⟨_, _, hval⟩ := outer_invariant fa ga
    (fun i hi => by rw [hfa]; exact fa_bound f i hi)
    (fun j => by
      by_cases hj : j < n
      · rw [hga]; exact fa_bound g j hj
      · rw [hga]; rw [Array.getD]; rw [dif_neg (by rw [Array.size_map, g.size_toArray]; omega)]
        simp [modulus])
    n (le_refl n)
  rw [hval k.val k.isLt]
  -- bridge the colVal sum to negacyclicConvCoeff
  rw [LatticeCrypto.negacyclicConvCoeff, Finset.sum_filter, Fintype.sum_prod_type]
  -- turn the LHS range×range sum into an iterated Fin sum to match the RHS
  rw [Finset.sum_product]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => ∑ j ∈ Finset.range n,
      if (i + j) % n = (k:ℕ) then colVal n fa ga i j else 0) n]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => if (i.val + j) % n = (k:ℕ) then colVal n fa ga i.val j else 0) n]
  apply Finset.sum_congr rfl
  intro j _
  -- termwise: colVal matches the spec summand via fa_cast
  by_cases hc : (i.val + j.val) % n = (k:ℕ)
  · rw [if_pos hc, if_pos hc]
    unfold colVal
    rw [hfa, hga, fa_cast f i.val i.isLt, fa_cast g j.val j.isLt]
  · rw [if_neg hc, if_neg hc]

/-- The `UInt64` accumulator of `pairL2NormSqU32` never overflows: folding a list of
nonnegative summands whose every prefix stays below `2 ^ 64` commutes with `UInt64.toNat`. -/
private theorem foldl_uint64_add_toNat {α : Type*} (g : α → UInt64) (l : List α)
    (init : UInt64)
    (hbound : ∀ pre, pre <+: l →
      init.toNat + (pre.map (fun a => (g a).toNat)).sum < 2 ^ 64) :
    (l.foldl (fun b a => b + g a) init).toNat
      = init.toNat + (l.map (fun a => (g a).toNat)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have hx : (init + g x).toNat = init.toNat + (g x).toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt]
      have := hbound [x] (by simp [List.prefix_cons_iff])
      simpa using this
    rw [ih (init + g x)]
    · rw [hx]; ring
    · intro pre hpre
      rw [hx]
      have := hbound (x :: pre) (by
        rcases hpre with ⟨t, rfl⟩
        exact ⟨t, by simp⟩)
      simp only [List.map_cons, List.sum_cons] at this
      omega

/-- An integer of magnitude below `2 ^ 63` is fixed by balanced reduction modulo `2 ^ 64`. -/
private theorem bmod_two_pow_64_eq_self (z : ℤ) (hlo : -(2 ^ 63) < z) (hhi : z < 2 ^ 63) :
    z.bmod (2 ^ 64) = z := by
  rw [Int.bmod_def]; push_cast; split_ifs <;> omega

/-- Widening a small `UInt32` to `Int64` preserves its value as an integer. -/
private theorem toInt_uint32_toInt64 (v : UInt32) (h : v.toNat < 12289) :
    v.toUInt64.toInt64.toInt = (v.toNat : ℤ) := by
  rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_bmod,
    UInt64.toNat_toBitVec, UInt32.toNat_toUInt64]
  rw [Int.bmod_eq_emod_of_lt]
  · exact Int.emod_eq_of_lt (by positivity) (by omega)
  · rw [Int.emod_eq_of_lt (by positivity) (by omega)]; omega

/-- The modulus widened to `Int64` reads back as the integer `modulus`. -/
private theorem toInt_modulus : modulus.toUInt64.toInt64.toInt = (modulus : ℤ) := by
  decide +kernel

/-- The `UInt32` packing of a residue's value round-trips to its `ZMod.val`. -/
private theorem val_toUInt32_toNat (x : ZMod modulus) :
    (ZMod.val x).toUInt32.toNat = ZMod.val x := by
  have hval : ZMod.val x < 12289 := ZMod.val_lt x
  change (UInt32.ofNat (ZMod.val x)).toNat = ZMod.val x
  rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)

/-- The centering branch in `pairL2NormSqU32` computes the integer `centeredRepr`. -/
private theorem kernelC_toInt (x : ZMod modulus) :
    (if (ZMod.val x).toUInt32 ≤ (modulus / 2).toUInt32 then
        (ZMod.val x).toUInt32.toUInt64.toInt64
      else (ZMod.val x).toUInt32.toUInt64.toInt64 - modulus.toUInt64.toInt64).toInt
      = LatticeCrypto.centeredRepr x := by
  have hval : ZMod.val x < 12289 := ZMod.val_lt x
  have hvn : (ZMod.val x).toUInt32.toNat = ZMod.val x := val_toUInt32_toNat x
  have hpos : (ZMod.val x).toUInt32.toUInt64.toInt64.toInt = (ZMod.val x : ℤ) := by
    rw [toInt_uint32_toInt64 _ (by omega), hvn]
  have hmod2 : (modulus : ℤ) / 2 = 6144 := by norm_num [modulus]
  have hcmp : ((ZMod.val x).toUInt32 ≤ (modulus / 2).toUInt32)
      ↔ ZMod.val x ≤ 6144 := by
    rw [UInt32.le_iff_toNat_le, hvn]
    have h2 : ((modulus / 2 : ℕ).toUInt32).toNat = 6144 := by
      change (UInt32.ofNat (modulus / 2)).toNat = 6144
      rw [UInt32.toNat_ofNat']; rfl
    rw [h2]
  by_cases h : ZMod.val x ≤ 6144
  · rw [if_pos (hcmp.mpr h), hpos, LatticeCrypto.centeredRepr_of_le (by omega)]
  · rw [if_neg (fun hc => h (hcmp.mp hc)), Int64.toInt_sub, hpos, toInt_modulus]
    have hgt : 6144 < ZMod.val x := by omega
    rw [LatticeCrypto.centeredRepr_of_gt (by omega),
      bmod_two_pow_64_eq_self _ (by omega) (by omega)]

/-- The per-coefficient `UInt64` summand contributed by index `a` of `s`. -/
private def loopG {n : ℕ} (s : Rq n) (a : ℕ) : UInt64 :=
  (let v := (ZMod.val (s.getD a 0)).toUInt32
   (if v ≤ (modulus / 2).toUInt32 then v.toUInt64.toInt64
    else v.toUInt64.toInt64 - modulus.toUInt64.toInt64) *
   (if v ≤ (modulus / 2).toUInt32 then v.toUInt64.toInt64
    else v.toUInt64.toInt64 - modulus.toUInt64.toInt64)).toUInt64

/-- In-range indexing through `Vector.getD` agrees with `Vector.get`. -/
private theorem getD_eq_get {n : ℕ} (s : Rq n) (i : ℕ) (hi : i < n) :
    Vector.getD s i 0 = s.get ⟨i, hi⟩ := by
  simp only [Vector.getD, Vector.get, Array.getD]
  have h2 : i < s.toArray.size := by rw [s.size_toArray]; exact hi
  rw [dif_pos h2]; rfl

/-- The per-coefficient summand equals the squared absolute centered representative. -/
private theorem loopG_toNat {n : ℕ} (s : Rq n) (a : ℕ) (ha : a < n) :
    (loopG s a).toNat = (LatticeCrypto.centeredRepr (s.get ⟨a, ha⟩)).natAbs ^ 2 := by
  rw [loopG, getD_eq_get s a ha]
  set x : ZMod modulus := s.get ⟨a, ha⟩
  set c : Int64 := if (ZMod.val x).toUInt32 ≤ (modulus / 2).toUInt32 then
      (ZMod.val x).toUInt32.toUInt64.toInt64
    else (ZMod.val x).toUInt32.toUInt64.toInt64 - modulus.toUInt64.toInt64 with hcdef
  have hcr : c.toInt = LatticeCrypto.centeredRepr x := kernelC_toInt x
  have habs : (LatticeCrypto.centeredRepr x).natAbs ≤ 6144 := by
    have := LatticeCrypto.centeredRepr_abs_le (q := modulus) x
    simpa [show modulus / 2 = 6144 from by norm_num [modulus]] using this
  have hbnd : -(6144 : ℤ) ≤ c.toInt ∧ c.toInt ≤ 6144 := by rw [hcr]; omega
  have hsq : (c * c).toInt = c.toInt * c.toInt := by
    rw [Int64.toInt_mul, bmod_two_pow_64_eq_self]
    · nlinarith [hbnd.1, hbnd.2]
    · nlinarith [hbnd.1, hbnd.2]
  have hle : (0 : Int64) ≤ c * c := by
    rw [Int64.le_iff_toInt_le, hsq]; exact mul_self_nonneg _
  rw [Int64.toNat_toUInt64_of_le hle, Int64.toNatClampNeg, hsq, hcr,
    ← Int.natAbs_mul_self, Int.toNat_natCast, ← sq]

/-- Each per-coefficient summand is bounded by `(modulus / 2) ^ 2 = 6144 ^ 2`. -/
private theorem loopG_toNat_le {n : ℕ} (s : Rq n) (a : ℕ) (ha : a < n) :
    (loopG s a).toNat ≤ 6144 ^ 2 := by
  rw [loopG_toNat s a ha]
  have := LatticeCrypto.centeredRepr_abs_le (q := modulus) (s.get ⟨a, ha⟩)
  have h6 : (LatticeCrypto.centeredRepr (s.get ⟨a, ha⟩)).natAbs ≤ 6144 := by
    simpa [show modulus / 2 = 6144 from by norm_num [modulus]] using this
  exact Nat.pow_le_pow_left h6 2

/-- Every prefix sum of one loop's summands stays below `n * 6144 ^ 2`. -/
private theorem loopG_prefix_sum_le {n : ℕ} (s : Rq n) (pre : List ℕ)
    (hpre : pre <+: List.range n) :
    (pre.map (fun a => (loopG s a).toNat)).sum ≤ n * 6144 ^ 2 := by
  have hlen : pre.length ≤ n := by simpa using hpre.length_le
  have hsub : ∀ a ∈ pre, a < n := fun a ha => by simpa using hpre.mem ha
  calc (pre.map (fun a => (loopG s a).toNat)).sum
      ≤ (pre.map (fun _ => 6144 ^ 2)).sum :=
        List.sum_le_sum (fun a ha => loopG_toNat_le s a (hsub a ha))
    _ = pre.length * 6144 ^ 2 := by rw [List.map_const']; simp [List.sum_replicate]
    _ ≤ n * 6144 ^ 2 := Nat.mul_le_mul_right _ hlen

/-- A sum of `f` over `List.range n` rewrites as a `Finset` sum over `Fin n`. -/
private theorem sum_map_range_eq_sum_fin {n : ℕ} (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]
    simp

set_option maxHeartbeats 1000000 in
-- The two-loop unfolding plus the nested no-overflow accumulator rewrites push elaboration
-- past the default heartbeat budget.
/-- The `Int64`/`UInt64` fast squared-ℓ₂ norm agrees with the abstract `pairL2NormSq`.

The hypothesis `2 * n * (modulus / 2) ^ 2 < 2 ^ 64` rules out `UInt64` wraparound in the
accumulator: the kernel sums `2 * n` centered squares, each at most `(modulus / 2) ^ 2`, so the
bound guarantees the running total stays below `2 ^ 64`. It holds with vast headroom for every
Falcon degree (`n ∈ {512, 1024}`). -/
theorem pairL2NormSqU32_eq_pairL2NormSq {n : ℕ} (hn : 2 * n * (modulus / 2) ^ 2 < 2 ^ 64)
    (s₁ s₂ : Rq n) :
    pairL2NormSqU32 s₁ s₂ = Falcon.pairL2NormSq s₁ s₂ := by
  have hrhs : Falcon.pairL2NormSq s₁ s₂ =
      (∑ i : Fin n, (LatticeCrypto.centeredRepr (s₁.get i)).natAbs ^ 2)
      + (∑ i : Fin n, (LatticeCrypto.centeredRepr (s₂.get i)).natAbs ^ 2) := by
    unfold Falcon.pairL2NormSq Falcon.normOps LatticeCrypto.NormOps.pairL2NormSq
      LatticeCrypto.zmodPolyNormOps LatticeCrypto.normOpsOfCenteredView
    simp only [LatticeCrypto.l2NormSqOf]; rfl
  rw [hrhs]
  unfold pairL2NormSqU32
  simp only [Id.run, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one,
    map_pure, List.forIn_pure_yield_eq_foldl, Nat.add_sub_cancel,
    ← List.range_eq_range']
  change (List.foldl (fun b a => b + loopG s₂ a)
        (List.foldl (fun b a => b + loopG s₁ a) 0 (List.range n)) (List.range n)).toNat = _
  have hbnd : n * 6144 ^ 2 + n * 6144 ^ 2 < 2 ^ 64 := by
    have h6 : (modulus / 2) ^ 2 = 6144 ^ 2 := by norm_num [modulus]
    rw [h6] at hn
    calc n * 6144 ^ 2 + n * 6144 ^ 2 = 2 * n * 6144 ^ 2 := by ring
      _ < 2 ^ 64 := hn
  have hi0 : (0 : UInt64).toNat = 0 := by simp
  have hpre1 : ∀ pre : List ℕ, pre <+: List.range n →
      (0 : UInt64).toNat + (pre.map (fun a => (loopG s₁ a).toNat)).sum < 2 ^ 64 := by
    intro pre hpre
    have hle := loopG_prefix_sum_le s₁ pre hpre
    rw [hi0]
    calc 0 + (pre.map (fun a => (loopG s₁ a).toNat)).sum
        = (pre.map (fun a => (loopG s₁ a).toNat)).sum := by ring
      _ ≤ n * 6144 ^ 2 := hle
      _ ≤ n * 6144 ^ 2 + n * 6144 ^ 2 := Nat.le_add_right _ _
      _ < 2 ^ 64 := hbnd
  have hi1 : (List.foldl (fun b a => b + loopG s₁ a) 0 (List.range n)).toNat
      ≤ n * 6144 ^ 2 := by
    rw [foldl_uint64_add_toNat (loopG s₁) (List.range n) 0 hpre1, hi0, Nat.zero_add]
    simpa using loopG_prefix_sum_le s₁ (List.range n) (List.prefix_refl _)
  have hpre2 : ∀ pre : List ℕ, pre <+: List.range n →
      (List.foldl (fun b a => b + loopG s₁ a) 0 (List.range n)).toNat
        + (pre.map (fun a => (loopG s₂ a).toNat)).sum < 2 ^ 64 := by
    intro pre hpre
    have h2 := loopG_prefix_sum_le s₂ pre hpre
    calc (List.foldl (fun b a => b + loopG s₁ a) 0 (List.range n)).toNat
          + (pre.map (fun a => (loopG s₂ a).toNat)).sum
        ≤ n * 6144 ^ 2 + n * 6144 ^ 2 := Nat.add_le_add hi1 h2
      _ < 2 ^ 64 := hbnd
  rw [foldl_uint64_add_toNat (loopG s₂) (List.range n) _ hpre2]
  rw [foldl_uint64_add_toNat (loopG s₁) (List.range n) 0 hpre1]
  rw [hi0, Nat.zero_add]
  rw [sum_map_range_eq_sum_fin, sum_map_range_eq_sum_fin]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _; rw [loopG_toNat _ i.val i.isLt]
  · apply Finset.sum_congr rfl
    intro i _; rw [loopG_toNat _ i.val i.isLt]

/-! ## Abstract primitives instance -/

private def samplerSeedBytes : Nat := 56

private noncomputable def realTwoPow (e : Int) : ℝ :=
  if 0 ≤ e then
    (2 : ℝ) ^ Int.toNat e
  else
    ((2 : ℝ) ^ Int.toNat (-e))⁻¹

@[reducible] private noncomputable def realSamplerFloatLike : FloatLike ℝ where
  zero := 0
  one := 1
  neg := Neg.neg
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  sqrt := Real.sqrt
  ofInt i := (i.toInt : ℝ)
  ofInt32 i := (i.toInt : ℝ)
  scaled i sc := (i.toInt : ℝ) * realTwoPow sc.toInt
  rint x := (round x).toInt64
  floor_ x := (⌊x⌋).toInt64
  expm_p63 x ccs :=
    let y : ℝ := ((2 : ℝ) ^ 63) * ccs * Real.exp (-x)
    if 0 ≤ y then
      (⌊y⌋).toInt64.toUInt64
    else
      0
  ofRawFPR x := ((Float.ofBits x).toRat0 : ℝ)

private def sampleSamplerSeed : ProbComp ByteArray := do
  let bytes ← ProbComp.sampleIID samplerSeedBytes ($ᵗ UInt8)
  return ByteArray.mk <| Array.ofFn fun i : Fin samplerSeedBytes => bytes i

private noncomputable def fxrScale : ℝ := (2 : ℝ) ^ (32 : Nat)

/-- Interpret an `FXR` word as its signed 32.32 fixed-point real value. -/
private noncomputable def fxrToReal (x : FXR.FXR) : ℝ :=
  (x.toInt64.toInt : ℝ) / fxrScale

/-- Encode a real number into Falcon's signed 32.32 fixed-point format by rounding
to the nearest scaled integer. -/
private noncomputable def realToFXR (x : ℝ) : FXR.FXR :=
  (round (x * fxrScale)).toInt64.toUInt64

/-- Convert an `R_q` polynomial to the coefficient array expected by the concrete FFT code. -/
private def rqToInt32Array (p : Params) (f : Rq p.n) : Array Int32 :=
  (Array.range p.n).map fun i => (ZMod.val (f.getD i 0)).toInt32

/-- Convert an integer polynomial to the coefficient array expected by the concrete FFT code. -/
private def intPolyToInt32Array (p : Params) (f : IntPoly p.n) : Array Int32 :=
  (Array.range p.n).map fun i => (f.getD i 0).toInt32

/-- Read Falcon's packed FXR FFT layout into the proof-level packed real vector. -/
private noncomputable def fxrArrayToRealFFTPoly (p : Params) (f : Array FXR.FXR) :
    RealFFTPoly p.fftDepth :=
  Vector.ofFn fun i => fxrToReal (f.getD i.1 0)

/-- Re-encode a proof-level packed FFT vector into Falcon's concrete FXR layout. -/
private noncomputable def realFFTPolyToFXRArray (p : Params) (f : RealFFTPoly p.fftDepth) :
    Array FXR.FXR :=
  (Array.range p.n).map fun i =>
    if h : i < 2 * 2 ^ p.fftDepth then
      realToFXR (f.get ⟨i, h⟩)
    else
      0

/-- Convert concrete FXR coefficients back to an integer polynomial via Falcon's
reference fixed-point rounding rule. -/
private def fxrArrayToIntPoly (p : Params) (f : Array FXR.FXR) : IntPoly p.n :=
  Vector.ofFn fun i => (FXR.fxrRound (f.getD i.1 0)).toInt

/-- Concrete Falcon primitive bundle used to connect the executable code to the abstract
Falcon interfaces. -/
noncomputable def concretePrimitives (p : Params) (hn : p.n = 2 ^ p.logn) :
    Primitives p where
  publicKeyBytes := fun h => publicKeyBytes p.logn h
  hashToPoint := fun salt pkBytes msg => hashToPoint p.n salt pkBytes msg
  samplerZ := fun μ σ => do
    let seed ← sampleSamplerSeed
    let state := SamplerZ.PRNGState.init seed
    letI : FloatLike ℝ := realSamplerFloatLike
    let (z, _) := SamplerZ.samplerZ p.logn state μ σ⁻¹
    return z.toInt
  fftTarget := fun c =>
    fxrArrayToRealFFTPoly p <| FXR.vectFFT p.logn <| FXR.vectSet p.logn (rqToInt32Array p c)
  fftInt := fun f =>
    fxrArrayToRealFFTPoly p <| FXR.vectFFT p.logn <| FXR.vectSet p.logn (intPolyToInt32Array p f)
  ifftRound := fun f =>
    fxrArrayToIntPoly p <| FXR.vectIFFT p.logn (realFFTPolyToFXRArray p f)
  compress := compress p.n
  decompress := decompress p.n
  nttOps := hn ▸ concreteNTTRingOps p.logn

/-- `publicKeyBytes` for `concretePrimitives` unfolds to the concrete Falcon encoder. -/
@[simp] theorem concretePrimitives_publicKeyBytes_eq
    (p : Params) (hn : p.n = 2 ^ p.logn) (h : Rq p.n) :
    (concretePrimitives p hn).publicKeyBytes h = publicKeyBytes p.logn h := by rfl

/-- `hashToPointForPublicKey` for `concretePrimitives` unfolds to the concrete FN-DSA hash path. -/
@[simp] theorem concretePrimitives_hashToPointForPublicKey_eq
    (p : Params) (hn : p.n = 2 ^ p.logn) (h : Rq p.n)
    (salt : Bytes 40) (msg : List Byte) :
    (concretePrimitives p hn).hashToPointForPublicKey h salt msg =
      hashToPoint p.n salt (publicKeyBytes p.logn h) msg := by rfl

/-! ## Named bundles -/

/-- Concrete primitives specialized to Falcon-512. -/
noncomputable def falcon512Primitives : Primitives falcon512 :=
  concretePrimitives falcon512 rfl

/-- Concrete primitives specialized to Falcon-1024. -/
noncomputable def falcon1024Primitives : Primitives falcon1024 :=
  concretePrimitives falcon1024 rfl

end Falcon.Concrete
