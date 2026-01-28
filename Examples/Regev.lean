import VCVio

/-!
# The Regev encryption scheme

This file contains the implementation of the Regev encryption scheme, as well as some useful lemmas
for the proof of correctness.

NOTE: since the update to `v4.22.0-rc2`, there is no longer an automatic coercion from `ℕ` to `Fin
n` via taking modulo `n`. This breaks the proofs. Someone should fix this.
-/

open Mathlib OracleSpec OracleComp AsymmEncAlg

/-- The uniform error sampling distribution, from the range `[-χ, χ]` inside `Fin p` -/
def uniformErrSamp {p : ℕ} (χ : ℕ) (hχ : p > 2*χ) : ProbComp (Fin p) := do
  let e ←$ᵗ Fin (2*χ + 1)
  haveI : NeZero p := ⟨by omega⟩
  return (Fin.castLE hχ e) - ⟨χ, by omega⟩

/-- General form of the Regev encryption scheme, with a custom error sampling distribution -/
def regevAsymmEnc (n m p : ℕ) [hp2 : p.AtLeastTwo] (errSampKG : ProbComp (Fin p)) :
    AsymmEncAlg ProbComp (M := Bool) (PK := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m)
     (SK := Vector (Fin p) n) (C := Vector (Fin p) n × Fin p) where
  keygen := do
    let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let s ←$ᵗ Vector (Fin p) n
    let e ← (Vector.range m).mapM (fun _ ↦ errSampKG)
    return ((A, Vector.ofFn (Matrix.vecMul s.get A) + e), s)
  encrypt := λ (A, y) msg ↦ do
    let r2 ←$ᵗ Vector (Fin 2) m
    let r := (r2.map (Fin.castLE hp2.one_lt)).get
    let yr := dotProduct y.get r
    let signal := if msg then 0 else p / 2
    return (Vector.ofFn (Matrix.mulVec A r), yr + (Fin.ofNat p signal))
  decrypt := λ s (a, b) ↦ do
    let sa := dotProduct s.get a.get
    let val := Fin.val (sa - b)
    return if val < p/4 then true else val > 3*p/4
  __ := ExecutionMethod.default

lemma relax_p_bound {p χ m: ℕ} [hm : NeZero m] (h : p > 4 * (χ * m + 1)) : p > 2 * χ := by
  calc p > 4 * (χ * m + 1) := h
  _ ≥ 4 * (χ * m) := by omega
  _ ≥ 2 * (χ * m) := by omega
  _ ≥ 2 * χ := by
    rw [← mul_assoc]
    exact Nat.le_mul_of_pos_right (2 * χ) hm.one_le

def uniformRegevAsymmEnc (n m p : ℕ) [hp2 : p.AtLeastTwo] [NeZero m]
    (χ : ℕ) (he : p > 4*(χ*m + 1)) :=
  regevAsymmEnc n m p (uniformErrSamp χ (relax_p_bound he))

-- Note: we want to defer the condition `p > 4*(χ*m + 1)` until the proof of correctness

section useful_lemmas
-- Useful lemmas for the proof

def Fin_Bound {n : ℕ} (x : Fin n) (b : ℕ) : Prop :=
  x.val ≤ b ∨ x.val + b ≥ n

def Fin_Bound_vec {n m : ℕ} (v : Vector (Fin n) m) (b : ℕ) : Prop :=
  ∀ i, Fin_Bound (v.get i) b

@[simp]
lemma Fin_Bound_modulus {n : ℕ} (x : Fin n) : Fin_Bound x n := by
  left; simp

@[simp]
lemma Fin_Bound_ge {n b₁ b₂ : ℕ} {x : Fin n} (h : Fin_Bound x b₁)
 (g : b₁ ≤ b₂) : Fin_Bound x b₂ := by
  cases h
  · left; omega
  · right; omega

@[simp]
lemma Fin_bound_zero {n : ℕ} (x : Fin n) : Fin_Bound x 0 ↔ x.val = 0:= by
  constructor <;> intro h
  · rcases h with h | h
    · omega
    · simp at h
      linarith [x.isLt]
  · left; linarith

@[simp]
lemma Fin_Bound_add {n b₁ b₂ : ℕ} {x y : Fin n} (h₁ : Fin_Bound x b₁)
 (h₂ : Fin_Bound y b₂) : Fin_Bound (x + y) (b₁ + b₂) := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · left
      rw [Fin.val_add_eq_ite]
      by_cases h : n ≤ x.val + y.val <;> simp [h] <;> linarith
    · by_cases h : n ≤ x.val + y.val
      · left
        simp [Fin.val_add_eq_ite, h]
        linarith [y.isLt]
      · right
        simp [Fin.val_add_eq_ite, h]
        omega
  · rcases h₂ with h₂ | h₂
    · by_cases h : n ≤ x.val + y.val
      · left
        simp [Fin.val_add_eq_ite, h]
        linarith [x.isLt]
      · right
        simp [Fin.val_add_eq_ite, h]
        linarith [x.isLt]
    · right
      rw [Fin.val_add_eq_ite]
      by_cases h : n ≤ x.val + y.val <;> simp [h] <;> omega

lemma Fin_bound_mul_helper {n b₁ b₂ : ℕ} {x y : Fin n} (h : b₁ * b₂ < n)
  (h₁ : x.val ≤ b₁) (h₂ : y.val + b₂ ≥ n) : Fin_Bound (x * y) (b₁ * b₂) := by
  by_cases g : x.val = 0
  · left; simp [Fin.val_mul, g]
  right
  rw [Fin.val_mul]
  have hy : y.val < n := y.isLt
  have hc : ∃ c ≤ b₂, y.val + c = n := by
    use n - y.val; constructor <;> omega
  rcases hc with ⟨c, hc1, hc2⟩
  have h3 : x.val * y.val + x.val * c = n * x.val := by
    rw [← mul_add, hc2]; apply mul_comm
  calc x.val * y.val % n + b₁ * b₂ ≥ x.val * y.val % n + b₁ * b₂ := by rfl
    _ ≥ x.val * y.val % n + b₁ * c :=
      Nat.add_le_add_left (Nat.mul_le_mul_left b₁ hc1) _
    _ ≥ x.val * y.val % n + x.val * c := by
      apply Nat.mul_le_mul_left c at h₁
      apply Nat.add_le_add_left
      linarith [h₁]
    _ ≥ x.val * y.val % n + x.val * c % n := by
      apply Nat.add_le_add_left
      exact Nat.mod_le (x.val * c) n
    _ ≥ n := by
      contrapose g; simp at g; simp
      apply Nat.add_mod_of_add_mod_lt at g
      rw [h3, Nat.mul_mod_right] at g
      symm at g
      rw [Nat.add_eq_zero] at g
      rcases g with ⟨g1, g2⟩
      have : x.val * c < n := by
        apply lt_of_le_of_lt _ h
        trans (b₁ * c)
        exact Nat.mul_le_mul_right c h₁
        exact Nat.mul_le_mul_left b₁ hc1
      apply Nat.mod_eq_of_lt at this
      have hcn0 : c ≠ 0 := by omega
      rw [g2] at this
      symm at this; apply mul_eq_zero.1 at this
      tauto

@[simp]
lemma Fin_Bound_mul {n b₁ b₂ : ℕ} {x y : Fin n} (h₁ : Fin_Bound x b₁)
 (h₂ : Fin_Bound y b₂) : Fin_Bound (x * y) (b₁ * b₂) := by
  by_cases h : (b₁ * b₂) ≥ n
  · apply Fin_Bound_ge (Fin_Bound_modulus (x * y)) h
  simp at h
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · left
      rw [Fin.val_mul]
      apply le_trans (Nat.mod_le (x.val * y.val) n)
      trans x.val * b₂
      · apply mul_le_mul_left' h₂
      · apply mul_le_mul_right' h₁
    · apply Fin_bound_mul_helper h h₁ h₂
  · rcases h₂ with h₂ | h₂
    · nth_rw 2 [mul_comm]
      rw [mul_comm]
      rw [mul_comm] at h
      apply Fin_bound_mul_helper h h₂ h₁
    · left
      by_cases g : n = 0
      · omega
      have g : NeZero n := ⟨by omega⟩
      stop
      generalize hx : Fin.sub n x = x'
      generalize hy : Fin.sub n y = y'
      have h3 : x + x' = 0 := by
        rw [← hx]; simp
        show x + (0 - x) = 0
        simp
      have h4 : y + y' = 0 := by
        rw [← hy]; simp
        show y + (0 - y) = 0
        simp
      have h5 : x * y = x' * y' := by
        have : x * y = (x + x') * (y + y') + x' * y' - x' * (y + y') - y' * (x + x') := by
          ring
        rw [this, h3, h4]
        ring
      rw [h5, Fin.val_mul]
      apply le_trans (Nat.mod_le (x'.val * y'.val) n)
      trans x'.val * b₂
      · apply mul_le_mul_left'
        rw [←hy, Fin.sub, Fin.val]; simp
        apply le_trans (Nat.mod_le (n - ↑y) n)
        simp
        linarith
      · apply mul_le_mul_right'
        rw [←hx, Fin.sub, Fin.val]; simp
        apply le_trans (Nat.mod_le (n - ↑x) n)
        simp
        linarith

@[simp]
lemma Fin_bound_neg {n b : ℕ} {x : Fin n} (h : Fin_Bound x b) :
  Fin_Bound (-x) b := by
  rcases n with _ | n
  · cases x; omega
  · rcases x with ⟨_ | _, _⟩
    · simpa
    · simp only [Fin_Bound, ge_iff_le, Fin.neg_def] at *
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

lemma Fin_bound_dotprod {p m b₁ b₂ : ℕ} {v₁ v₂ : Vector (Fin p) m}
(h1 : Fin_Bound_vec v₁ b₁) (h2 : Fin_Bound_vec v₂ b₂) (Nez : NeZero p) :
  Fin_Bound (dotProduct v₁.get v₂.get) (b₁ * b₂ * m) := by
  rw [dotProduct]
  generalize hf : (fun i ↦ v₁.get i * v₂.get i) = f
  have : ∀ i, Fin_Bound (f i) (b₁ * b₂) := by
    intro i
    simp_rw [← hf]
    apply Fin_Bound_mul (h1 i) (h2 i)
  generalize hb : b₁ * b₂ = b
  rw [hb] at this
  clear hf hb h1 h2 v₁ v₂ b₁ b₂
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.univ_castSuccEmb]
    simp
    rw [add_comm, ← Fin.sum_univ_castSucc]
    sorry
    -- · apply Fin_Bound_add
    --   · simp
    --     apply ih
    --     intro i
    --     rw [Fin.castLE]
    --     apply this
    --   · apply this
    -- simp
    -- intro ⟨i, hi⟩ hl
    -- rw [Fin.castLE, Fin.last] at hl
    -- simp at hl
    -- linarith

@[simp]
lemma Fin_bound_castLE {n m : ℕ} {x : Fin (n + 1)} {h : n < m} :
  Fin_Bound (Fin.castLE h x) n := by
  left; simp; omega

lemma IntLE_imp_NatLE {a b : ℕ} (h : (a : ℤ) ≤ (b : ℤ)) : a ≤ b := by omega

lemma Fin_bound_shift_cast {p χ} {a : Fin (2*χ + 1)} [NeZero p] (h : p > 2*χ) :
    Fin_Bound (Fin.castLE h a - (Fin.ofNat p χ)) χ := by
  by_cases n0 : χ = 0
  · have := Fin.le_val_last a
    simp [n0, Fin.ofNat] at *
    sorry
  by_cases hv : a ≥ χ
  · left
    simp at *
    apply IntLE_imp_NatLE
    rw [Fin.intCast_val_sub_eq_sub_add_ite]
    simp
    stop
    have : ↑χ ≤ Fin.castLE h a := by
      simp [hv]
      rw [Fin.le_def] at hv ⊢
      trans ↑a <;> simp at *
      rw [Nat.mod_eq_of_lt] at hv ⊢ <;> omega
    simp_all [Fin.ofNat, this]
    trans 2 * χ
    · omega
    · simp [Fin.castLE] at this
      rw [Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt] <;> linarith
  · right
    simp at *
    apply IntLE_imp_NatLE; simp
    rw [Fin.intCast_val_sub_eq_sub_add_ite]; simp
    stop
    have : ↑χ > Fin.castLE h a := by
      simp [hv]
      rw [Fin.lt_def] at hv ⊢
      apply lt_of_le_of_lt
      simp at *
      apply le_refl
      simp at *
      rw [Nat.mod_eq_of_lt] at hv ⊢ <;> omega
    rw [ite_cond_eq_false]
    · simp only [Fin.ofNat, Fin.ofNat_eq_cast, Fin.val_natCast, Int.natCast_emod, ge_iff_le]
      rw [Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt] <;> linarith
    simp_all [Fin.ofNat, this]

-- This lemma is no longer needed
lemma Fin_bound_shift_cast_vec {p χ m : ℕ} {v : Vector (Fin (2*χ + 1)) m} [NeZero p] (h : p > 2*χ) :
    Fin_Bound_vec (v.map (fun t ↦ (Fin.castLE h t) - (Fin.ofNat p χ))) χ := by
  intro i
  simp [Vector.get]
  apply Fin_bound_shift_cast h

end useful_lemmas

namespace Regev

variable {n m p : ℕ} [hp2 : p.AtLeastTwo]

section correct

/-- Correctness of the Regev encryption scheme, with respect to the uniform error sampling
  distribution in `[-χ, χ]`.

  This is where we add the extra parameter `χ`, and the conditions `m > 0` and `p > 4*(χ*m + 1)` -/
theorem isCorrect_of_uniformErrSamp [hm : NeZero m] (χ : ℕ) (he: p > 4*(χ*m + 1)) :
    (regevAsymmEnc n m p (uniformErrSamp χ (relax_p_bound he))).PerfectlyCorrect := by
  rintro msg
  simp [CorrectExp, regevAsymmEnc, uniformErrSamp]
  rintro A s err h' r
  generalize h1 : (Vector.map (Fin.castLE hp2.one_lt) r) = rv
  have pne0 : NeZero p := ⟨by omega⟩
  have herr: p > 2*χ := (relax_p_bound (hm := hm) he)
  rw [← Matrix.dotProduct_mulVec]
  generalize h2 : -(err.get ⬝ᵥ rv.get) = mask
  have : χ * m ≤ p / 4 - 1:= by
    simp at he
    rw [mul_comm] at he
    apply le_of_lt at he
    have : 0 < 4 := by linarith
    apply (Nat.le_div_iff_mul_le this).2 at he
    omega
  have mask_bound : Fin_Bound mask (χ * m) := by
    rw [← mul_one χ, ← h2, ← h1]
    apply Fin_bound_neg
    apply Fin_bound_dotprod
    · intro i
      apply mem_support_vector_mapM.mp at h'
      have : err.get i = err[i.1] := by aesop
      rw [this]
      have := h' i
      simp at this
      obtain ⟨y, hy⟩ := this
      rw [← hy]
      stop
      exact Fin_bound_shift_cast herr
    · intro i
      simp [Vector.get]
  apply Fin_Bound_ge mask_bound at this
  cases msg <;> simp
  · constructor <;> ring_nf <;> stop rw [h2] <;>
    rcases this with h | h <;> rw [Fin.sub_def, Fin.val] <;> simp
  --   · rw [Nat.mod_eq_of_lt]
  --     · rw [Nat.mod_eq_of_lt] <;> omega
  --     rw [Nat.mod_eq_of_lt] <;> omega
  --   · rw [Nat.mod_eq_sub_mod]
  --     · rw [Nat.mod_eq_of_lt] <;> rw [Nat.mod_eq_of_lt] <;> omega
  --     · rw [Nat.mod_eq_of_lt] <;> omega
  --   · rw [Nat.mod_eq_of_lt]
  --     · rw [Nat.mod_eq_of_lt] <;> omega
  --     rw [Nat.mod_eq_of_lt] <;> omega
  --   · rw [Nat.mod_eq_sub_mod]
  --     · rw [Nat.mod_eq_of_lt] <;> rw [Nat.mod_eq_of_lt] <;> omega
  --     rw [Nat.mod_eq_of_lt] <;> omega
  · stop
    rw [h2]
    rcases this with h | h
    · left; omega
    · right; omega

end correct

section security

-- Original hybrid (hybrid 0) is the IND-CPA experiment

variable [NeZero m] {χ} {he: p > 4*(χ*m + 1)}
  -- (lwe_adv : Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m → ProbComp Bool)
  (adv : IND_CPA_Adv (uniformRegevAsymmEnc n m p χ he))

-- noncomputable def LWE_Advantage : ℝ :=
--   (LWE_Experiment n m p (uniformErrSamp χ (by sorry)) adv).advantage

-- Want to show:
-- ∀ adv in hybrid 0,
  -- advantage (hybrid 0, adv) ≤ advantage (hybrid 1, reduction1 (adv)) + advantage (LWE game, ...)
-- ∀ adv in hybrid 1, advantage (hybrid 1, adv) ≤ advantage (hybrid 2, reduction2 (adv))

def Hybrid_0 : ProbComp Bool :=
  IND_CPA_OneTime_Game (encAlg := uniformRegevAsymmEnc n m p χ he) adv

example : Hybrid_0 adv = IND_CPA_OneTime_Game adv := by
  rfl
  -- simp [IND_CPA_OneTime_Game, regevAsymmEnc]

-- What Hybrid 0 looks like:
-- do
--   let b ← $ᵗBool
--   let x ← $ᵗMatrix (Fin n) (Fin m) (Fin p)
--   let x_1 ← $ᵗVector (Fin p) n
--   let a ← $ᵗVector (Fin (2 * χ + 1)) m
--   let __discr ←
--     adv.chooseMessages (x, Vector.ofFn (Matrix.vecMul x_1.get x) +
--       Vector.map (fun t ↦ Fin.castLE ⋯ t - ↑χ) a)
--   let a_1 ← $ᵗVector (Fin 2) m
--   let b' ←
--     adv.distinguish __discr.2.2
--         (Vector.ofFn (x.mulVec (Vector.map (Fin.castLE hp2) a_1).get),
--           Matrix.vecMul x_1.get x ⬝ᵥ (Vector.map (Fin.castLE hp2) a_1).get +
--               (Vector.map (fun t ↦ Fin.castLE ⋯ t - ↑χ) a).get ⬝ᵥ
--                 (Vector.map (Fin.castLE hp2) a_1).get +
--             if if b = true then __discr.1 = true else __discr.2.1 = true
--               then 0 else ↑(p / 2))
--   if b = b' then pure () else failure

-- In Hybrid 1, we sample u = A s + e randomly instead
def Hybrid_1 : ProbComp Bool := do
  let b ←$ᵗ Bool
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  let ⟨m₁, m₂, st⟩ ← adv.chooseMessages (A, u)
  let c ← if b then (uniformRegevAsymmEnc n m p χ he).encrypt (A, u) m₁
    else (uniformRegevAsymmEnc n m p χ he).encrypt (A, u) m₂
  let b' ← adv.distinguish st c
  return b = b'

-- Hybrid 0 and Hybrid 1 are indistinguishable due to decisional LWE

def Hybrid_01_Reduction : LWE_Adversary n m p := fun Au => do
  let b ←$ᵗ Bool
  let ⟨m₁, m₂, st⟩ ← adv.chooseMessages Au
  let c ← if b then (uniformRegevAsymmEnc n m p χ he).encrypt Au m₁
  else (uniformRegevAsymmEnc n m p χ he).encrypt Au m₂
  let b' ← adv.distinguish st c
  return b'

/-- From an adversary that can distinguish between Hybrid 0 and Hybrid 1, we can construct an
adversary that can distinguish between LWE and the uniform distribution. -/
theorem Hybrid_0_ind_Hybrid_1 :
    (Hybrid_0 adv).advantage' ≤ (Hybrid_1 adv).advantage'
      + (LWE_Advantage n m p (uniformErrSamp χ (relax_p_bound he)) (Hybrid_01_Reduction adv)) := by
  unfold LWE_Advantage ProbComp.advantage' Hybrid_0 Hybrid_1 Hybrid_01_Reduction
    IND_CPA_OneTime_Game LWE_Experiment uniformRegevAsymmEnc
  -- An absolute mess, need to refactor games
  sorry

def Hybrid_2 : ProbComp Bool := do
  let b ←$ᵗ Bool
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  let ⟨_, _, st⟩ ← adv.chooseMessages (A, u)
  -- Don't know why have to sample `c₁` and `c₂` separately
  let c₁ ←$ᵗ Vector (Fin p) n
  let c₂ ←$ᵗ Fin p
  let b' ← adv.distinguish st (c₁, c₂)
  return b = b'

-- Hybrid 1 and Hybrid 2 are indistinguishable due to the leftover hash lemma (or LWE itself)

-- In other words, we will reduce to the fact that `(A.mulVec x, dotProd u x)` is
-- statistically indistinguishable from random

section LHL

-- TODO: define & prove the leftover hash lemma in the most generality
-- For now, just state the downstream consequence that we will need

def LHL_Consequence_Adv (n p : ℕ) := (Vector (Fin p) n) × (Fin p) → ProbComp Bool

def LHL_Consequence_Game_0 (adv : LHL_Consequence_Adv n p) : ProbComp Bool := do
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  let r2 ←$ᵗ Vector (Fin 2) m
  let r := (r2.map (Fin.castLE hp2.one_lt)).get
  adv (Vector.ofFn (Matrix.mulVec A r), dotProduct u.get r)

def LHL_Consequence_Game_1 (adv : LHL_Consequence_Adv n p) : ProbComp Bool := do
  let x ←$ᵗ Vector (Fin p) n
  let y ←$ᵗ Fin p
  adv (x, y)

noncomputable def LHL_Consequence_Advantage (adv : LHL_Consequence_Adv n p) : ℝ :=
  (LHL_Consequence_Game_0 (m := m) adv).advantage₂' (LHL_Consequence_Game_1 adv)

end LHL

def Hybrid_12_Reduction : LHL_Consequence_Adv n p := fun x => do
  let b ←$ᵗ Bool
  let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
  let u ←$ᵗ Vector (Fin p) m
  let ⟨_, _, st⟩ ← adv.chooseMessages (A, u)
  let b' ← adv.distinguish st x
  return b = b'

theorem Hybrid_1_ind_Hybrid_2 :
    (Hybrid_1 adv).advantage' ≤ (Hybrid_2 adv).advantage'
      + (LHL_Consequence_Advantage (m := m) (Hybrid_12_Reduction adv)) := by
  unfold LHL_Consequence_Advantage Hybrid_1 Hybrid_2 Hybrid_12_Reduction
    LHL_Consequence_Game_0 LHL_Consequence_Game_1 ProbComp.advantage' ProbComp.advantage₂'
    uniformRegevAsymmEnc regevAsymmEnc
  simp
  -- rw [probOutput_false_eq_probOutput_true_not]
  conv_lhs =>
    rw [probOutput_bind_eq_sum_fintype, probOutput_bind_eq_sum_fintype]
    simp
  -- Still a mess...
  sorry

-- Finally, Hybrid 2's advantage is zero, since `b` is uniform and have nothing to do with
-- other variables
theorem Hybrid_2_advantage_zero : (Hybrid_2 adv).advantage' = 0 := by
  unfold ProbComp.advantage' Hybrid_2
  simp [sub_eq_zero, probOutput_false_eq_probOutput_true_not, probOutput_bind_eq_sum_fintype]
  rw [add_comm]

-- Putting everything together, we get that the IND-CPA advantage of Regev is at most the sum of:
-- (1) the LWE advantage
-- (2) the LHL consequence advantage

theorem IND_CPA_advantage_le :
  IND_CPA_OneTime_Advantage (encAlg := uniformRegevAsymmEnc n m p χ he) adv ≤
    (LWE_Advantage n m p (uniformErrSamp χ (relax_p_bound he)) (Hybrid_01_Reduction adv))
      + (LHL_Consequence_Advantage (m := m) (Hybrid_12_Reduction adv)) := by
  calc
    _ = (Hybrid_0 adv).advantage' := rfl
    _ ≤ (Hybrid_1 adv).advantage' +
          (LWE_Advantage n m p (uniformErrSamp χ (relax_p_bound he)) (Hybrid_01_Reduction adv)) :=
        Hybrid_0_ind_Hybrid_1 adv
    _ ≤ (Hybrid_2 adv).advantage' +
          (LHL_Consequence_Advantage (m := m) (Hybrid_12_Reduction adv)) +
          (LWE_Advantage n m p (uniformErrSamp χ (relax_p_bound he))
            (Hybrid_01_Reduction adv)) := by
        gcongr
        exact Hybrid_1_ind_Hybrid_2 adv
    _ = _ := by
        rw [Hybrid_2_advantage_zero, zero_add, add_comm]

end security

end Regev
