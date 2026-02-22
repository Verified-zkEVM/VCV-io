/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.ProbComp

/-!
# Uniform Selection Over a Type

This file defines a typeclass `SampleableType β` for types `β` with a canonical uniform selection
operation, using the `ProbComp` monad.

As compared to `HasUniformSelect` this provides much more structure on the behavior,
enforcing that every possible output has the same output probability never fails.
-/

universe u v w

open ENNReal

/-- A `SampleableType β` instance means that `β` is a finite inhabited type,
with a computation `selectElem` that selects uniformly at random from the type.
This generally requires choosing some "canonical" ordering for the type,
so we include this to get a computable version of selection.
We also require that each element has the same probability of being chosen from by `selectElem`,
see `SampleableType.probOutput_uniformSample` for the reduction when `α` has a fintype instance
involving the explicit cardinality of the type. -/
class SampleableType (β : Type) where
  selectElem : ProbComp β
  mem_support_selectElem (x : β) : x ∈ support selectElem
  probOutput_selectElem_eq (x y : β) : Pr[= x | selectElem] = Pr[= y | selectElem]

/-- Select uniformly from the type `β` using a type-class provided definition.
NOTE: naming is somewhat strange now that `Fintype` isn't explicitly required. -/
def uniformSample (β : Type) [h : SampleableType β] :
    ProbComp β := h.selectElem

prefix : 90 "$ᵗ" => uniformSample

variable (α : Type) [hα : SampleableType α]

@[simp, grind =]
lemma probOutput_uniformSample [Fintype α] (x : α) :
    Pr[= x | $ᵗ α] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have : (Fintype.card α : ℝ≥0∞) = ∑ y : α, 1 :=
    by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  simp_rw [this, Finset.mul_sum, mul_one]
  rw [← sum_probOutput_eq_one (mx := $ᵗ α) (by aesop)]
  exact Finset.sum_congr rfl λ y _ ↦ SampleableType.probOutput_selectElem_eq x y

lemma probFailure_uniformSample : Pr[⊥ | $ᵗ α] = 0 := by aesop

@[simp] instance : NeverFail ($ᵗ α) := inferInstance

@[simp, grind =]
lemma evalDist_uniformSample [Fintype α] [Nonempty α] :
    evalDist ($ᵗ α) = liftM (PMF.uniformOfFintype α) := by aesop

@[simp, grind =]
lemma support_uniformSample : support ($ᵗ α) = Set.univ := by
  simp only [Set.ext_iff, Set.mem_univ, iff_true]
  apply SampleableType.mem_support_selectElem

lemma mem_support_uniformSample {x : α} : x ∈ support ($ᵗ α) := by grind

@[simp, grind =]
lemma finSupport_uniformSample [Fintype α] [DecidableEq α] :
    finSupport ($ᵗ α) = Finset.univ := by aesop

@[simp, grind =]
lemma probEvent_uniformSample [Fintype α] (p : α → Prop) [DecidablePred p] :
    Pr[p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp only [probEvent_eq_sum_filter_univ, probOutput_uniformSample, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]

section instances

instance (α : Type) [Unique α] : SampleableType α where
  selectElem := return default
  mem_support_selectElem x := Unique.eq_default x ▸ (by simp)
  probOutput_selectElem_eq x y := by rw [Unique.eq_default x, Unique.eq_default y]

instance : SampleableType Bool where
  selectElem := $! #v[true, false]
  mem_support_selectElem x := by simp
  probOutput_selectElem_eq x y := by simp

/-- Select a uniform element from `α × β` by independently selecting from `α` and `β`. -/
instance (α β : Type) [Fintype α] [Fintype β] [Inhabited α] [Inhabited β]
    [SampleableType α] [SampleableType β] : SampleableType (α × β) where
  selectElem := (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)
  mem_support_selectElem x := by simp
  probOutput_selectElem_eq := by
    stop
    simp only [Prod.forall, probOutput_seq_map_prod_mk_eq_mul,
      probOutput_uniformSample, forall_const, implies_true]

/-- Nonempty `Fin` types can be selected from, using implicit casting of `Fin (n - 1 + 1)`. -/
instance (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by simp

instance (n : ℕ) : SampleableType (ZMod (n + 1)) where
  selectElem := $[0..n]
  mem_support_selectElem := by grind
  probOutput_selectElem_eq x y := by grind

/-- Version of `Fin` selection using the `NeZero` typeclass, avoiding the need for `n + 1`. -/
instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) where
  selectElem := congr_arg Fin (Nat.succ_pred (NeZero.ne n)).symm ▸ $ᵗ (Fin (n - 1 + 1))
  mem_support_selectElem x := by sorry --rw [mem_support_eqRec_iff]; simp
  probOutput_selectElem_eq x y := by sorry --simp [probOutput_eqRec]

/-- Select a uniform element from `Vector α n` by independently selecting `α` at each index. -/
instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := by induction n with
  | zero => exact pure #v[]
  | succ m ih => exact Vector.push <$> ih <*> ($ᵗ α)
  mem_support_selectElem x := by induction n with
  | zero => simp
  | succ m ih =>
    stop
    simp [ih]
    use x.pop, x.back
    apply Vector.push_pop_back
  probOutput_selectElem_eq x y := by induction n with
  | zero =>
    have : x=y := by
      apply Vector.ext
      rintro i hi
      linarith
    simp [this]
    -- have : Subsingleton (Vector α 0) := by
    --   apply Vector.ext
    --   rintro i hi
    --   linarith
    -- Subsingleton
    -- simp [this]
  | succ m ih =>
    stop
    rw [← Vector.push_pop_back x, ← Vector.push_pop_back y]
    simp [probOutput_seq_map_vec_push_eq_mul, -Vector.push_pop_back]
    unfold uniformSample
    rw [SampleableType.probOutput_selectElem_eq x.back y.back]
    exact congrFun (congrArg HMul.hMul (ih x.pop y.pop)) Pr[= y.back | SampleableType.selectElem]

/-- Select a uniform element from `Matrix α n` by independently selecting `α` at each index. -/
instance (α : Type) (n m : ℕ) [SampleableType α] [DecidableEq α] :
    SampleableType (Matrix (Fin n) (Fin m) α) where
  -- selectElem := (fun x ↦ (fun i j ↦ x)) <$> ($ᵗ α)
  selectElem := by induction n with
  | zero => exact pure (Matrix.of ![])
  | succ n ihn => exact do
    let top ← $ᵗ Vector α m
    let bot ← ihn
    -- return Matrix.of (Fin.snoc top bot.get)
    return Fin.cons top.get bot
    -- return (Matrix.of (fun i j ↦ if h : i ≠ Fin.last n then top (Fin.castPred i h) j else bot[j]))
  mem_support_selectElem x := by induction n with
  | zero =>
    simp only [bind_pure_comp, Nat.rec_zero, support_pure, Set.mem_singleton_iff]
    apply Matrix.ext
    rintro i j
    exact False.elim (IsEmpty.false i)
  | succ p ih =>
    simp at *
    stop
    use Vector.ofFn (x 0), (Fin.tail x); constructor
    simp [ih]
    have : (Vector.ofFn (x 0)).get = x 0 := by
      ext i
      simp [Vector.get]
    simp [Fin.cons_self_tail, this]
  probOutput_selectElem_eq x y := by induction n with
  | zero =>
    simp
    rfl
  | succ m ih =>
    sorry

/-- A type equivalent to a `SampleableType` is also `SampleableType`. -/
def SampleableType.ofEquiv {α β : Type} [DecidableEq α] [DecidableEq β] [SampleableType α]
    (e : α ≃ β) : SampleableType β where
  selectElem := e <$> ($ᵗ α)
  mem_support_selectElem := fun x => by
    stop
    -- support (e <$> selectElem) = e '' support selectElem
    simp only [OracleComp.support_map]
    -- Since e is an equivalence, x ∈ e '' S ↔ e.symm x ∈ S
    rw [Set.mem_image_equiv]
    exact SampleableType.mem_support_selectElem (e.symm x)
  probOutput_selectElem_eq := fun x y => by
    stop
    simp only [probOutput_map_eq_tsum, OracleComp.probOutput_pure, mul_ite, mul_one, mul_zero]
    let reduce_sum (z : β) :
      (∑' a, if z = e a then Pr[= a | SampleableType.selectElem (β := α)] else 0)
      = Pr[= e.symm z | SampleableType.selectElem (β := α)] := by
      convert tsum_eq_single (e.symm z) _
      · simp only [Equiv.apply_symm_apply, ↓reduceIte]
      · intro b hb
        split_ifs with h
        · have h_eq: e.symm z = b := by rw [h, Equiv.symm_apply_apply]
          rw [←h_eq]; simp only [probOutput_eq_zero_iff']
          exact fun a ↦ hb (id (Eq.symm h_eq))
        · rfl
    rw [reduce_sum x, reduce_sum y]
    apply SampleableType.probOutput_selectElem_eq

/-- A function from `Fin n` to a `SampleableType` is also `SampleableType`. -/
instance instSampleableTypeFinFunc {n : ℕ} {α : Type} [SampleableType α] [DecidableEq α] :
    SampleableType (Fin n → α) := by
  letI instVectorFinFuncEquiv: (_root_.Vector α n) ≃ (Fin n → α) :=
    { toFun := fun v i => v.get i
      invFun := _root_.Vector.ofFn
      left_inv := fun v => by
        ext i
        simp only [Vector.ofFn, Vector.get, Fin.val_cast, Vector.getElem_toArray, Vector.getElem_mk,
          Array.getElem_ofFn]
      right_inv := fun f => by
        funext i
        simp only [Vector.get, Vector.ofFn, Fin.val_cast, Array.getElem_ofFn, Fin.eta] }
  exact SampleableType.ofEquiv (instVectorFinFuncEquiv)

end instances

-- TODO: generalize this lemma
/--
Given an independent probabilistic computation `ob : ProbComp Bool`, the probability that its
output `b'` differs from a uniformly chosen boolean `b` is the same as the probability that they
are equal. In other words, `P(b ≠ b') = P(b = b')` where `b` is uniform.
-/
lemma probOutput_uniformBool_not_decide_eq_decide {ob : ProbComp Bool} :
    Pr[= true | do let b ←$ᵗ Bool; let b' ← ob; return !decide (b = b')] =
      Pr[= true | do let b ←$ᵗ Bool; let b' ← ob; return decide (b = b')] := by
  stop
  simp [probOutput_bind_eq_sum_fintype, add_comm]
