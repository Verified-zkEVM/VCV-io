/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.BitVec
import VCVio.EvalDist.Bool

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

lemma probOutput_map_bijective_uniformSample [Fintype α]
    {f : α → α} (hf : Function.Bijective f) (x : α) :
    Pr[= x | f <$> ($ᵗ α)] = Pr[= x | $ᵗ α] := by
  obtain ⟨x', rfl⟩ := hf.surjective x
  rw [probOutput_map_injective ($ᵗ α) hf.injective x']
  exact SampleableType.probOutput_selectElem_eq _ _

/-- Pushing forward uniform sampling along a bijection preserves output probabilities. -/
lemma probOutput_map_bijective_uniform_cross
    {β : Type} [SampleableType β] [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Bijective f) (y : β) :
    Pr[= y | f <$> ($ᵗ α : ProbComp α)] = Pr[= y | ($ᵗ β : ProbComp β)] := by
  obtain ⟨x, rfl⟩ := hf.surjective y
  rw [probOutput_map_injective ($ᵗ α) hf.injective x,
      probOutput_uniformSample, probOutput_uniformSample,
      Fintype.card_of_bijective hf]

/-- Binding after pushing forward uniform sampling along a bijection preserves output
probabilities. -/
lemma probOutput_bind_bijective_uniform_cross
    {β γ : Type} [SampleableType β] [Fintype α]
    (f : α → β) (hf : Function.Bijective f) (g : β → ProbComp γ) (z : γ) :
    Pr[= z | ($ᵗ α : ProbComp α) >>= fun x => g (f x)] =
      Pr[= z | ($ᵗ β : ProbComp β) >>= fun y => g y] := by
  haveI := Fintype.ofBijective f hf
  have h : (($ᵗ α : ProbComp α) >>= fun x => g (f x)) =
      ((f <$> ($ᵗ α : ProbComp α)) >>= g) := by
    simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rw [h, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1
  funext y
  congr 1
  exact probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf y

lemma probOutput_add_left_uniform [AddGroup α] (m x : α) :
    Pr[= x | (fun y : α => m + y) <$> ($ᵗ α)] = Pr[= x | $ᵗ α] := by
  have h : Pr[= m + (-m + x) | (fun y : α => m + y) <$> ($ᵗ α)] =
      Pr[= -m + x | $ᵗ α] :=
    probOutput_map_injective
      (mx := ($ᵗ α))
      (f := fun y : α => m + y)
      (hf := by intro a b hab; exact add_left_cancel hab)
      (x := -m + x)
  calc
    Pr[= x | (fun y : α => m + y) <$> ($ᵗ α)]
        = Pr[= m + (-m + x) | (fun y : α => m + y) <$> ($ᵗ α)] := by
          congr 1
          symm
          exact add_neg_cancel_left m x
    _ = Pr[= -m + x | $ᵗ α] := h
    _ = Pr[= x | $ᵗ α] := by
          symm
          simpa [uniformSample] using
            (SampleableType.probOutput_selectElem_eq (β := α) x (-m + x))

lemma probOutput_bind_add_left_uniform [AddGroup α] {β : Type}
    (m : α) (f : α → ProbComp β) (z : β) :
    Pr[= z | (do let y ← $ᵗ α; f (m + y))] =
      Pr[= z | (do let y ← $ᵗ α; f y)] := by
  have hleft :
      (do let y ← $ᵗ α; f (m + y)) = (((fun y : α => m + y) <$> ($ᵗ α)) >>= fun y => f y) := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hleft, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun y => ?_
  rw [probOutput_add_left_uniform (α := α) m y]

/-- Pushing forward uniform sampling along a bijection preserves the full evaluation distribution. -/
lemma evalDist_map_bijective_uniform_cross
    {β : Type} [SampleableType β] [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Bijective f) :
    evalDist (f <$> ($ᵗ α : ProbComp α)) = evalDist ($ᵗ β : ProbComp β) := by
  apply evalDist_ext
  intro y
  exact probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf y

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
  probOutput_selectElem_eq x y := by
    classical
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    rw [probOutput_seq_map_eq_mul_of_injective2 ($ᵗ α) ($ᵗ β) Prod.mk
      (fun _ _ _ _ h => by cases h; aesop) x₁ x₂]
    rw [probOutput_seq_map_eq_mul_of_injective2 ($ᵗ α) ($ᵗ β) Prod.mk
      (fun _ _ _ _ h => by cases h; aesop) y₁ y₂]
    simp [probOutput_uniformSample]

/-- Nonempty `Fin` types can be selected from, using implicit casting of `Fin (n - 1 + 1)`. -/
instance (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by simp

/-- Version of `Fin` selection using the `NeZero` typeclass, avoiding the need for `n + 1`. -/
instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) where
  selectElem :=
    (Fin.cast (by
      simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
        (Nat.succ_pred (NeZero.ne n)))) <$> ($ᵗ (Fin (n - 1 + 1)))
  mem_support_selectElem x := by
    have hx : ∃ y : Fin (n - 1 + 1),
        Fin.cast (by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n))) y = x := by
      refine ⟨Fin.cast (by
        simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
          (Nat.succ_pred (NeZero.ne n)).symm) x, ?_⟩
      simp [Fin.cast_cast
        (h := by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n)).symm)
        (h' := by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n)))
        (i := x)]
    simpa [support_map] using hx
  probOutput_selectElem_eq x y := by
    have hx : Pr[= x |
        (Fin.cast (by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n)))) <$> ($ᵗ (Fin (n - 1 + 1)))] =
        Pr[= Fin.cast (by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n)).symm) x | $ᵗ (Fin (n - 1 + 1))] := by
      simpa using
        (probOutput_map_injective ($ᵗ (Fin (n - 1 + 1)))
          (Fin.cast_injective (by
            simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
              (Nat.succ_pred (NeZero.ne n))))
          (Fin.cast (by
            simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
              (Nat.succ_pred (NeZero.ne n)).symm) x))
    have hy : Pr[= y |
        (Fin.cast (by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n)))) <$> ($ᵗ (Fin (n - 1 + 1)))] =
        Pr[= Fin.cast (by
          simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
            (Nat.succ_pred (NeZero.ne n)).symm) y | $ᵗ (Fin (n - 1 + 1))] := by
      simpa using
        (probOutput_map_injective ($ᵗ (Fin (n - 1 + 1)))
          (Fin.cast_injective (by
            simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
              (Nat.succ_pred (NeZero.ne n))))
          (Fin.cast (by
            simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using
              (Nat.succ_pred (NeZero.ne n)).symm) y))
    rw [hx, hy]
    exact SampleableType.probOutput_selectElem_eq _ _

/-- Version of `ZMod` selection using the `NeZero` typeclass, matching `Fin n`. -/
instance (n : ℕ) [hn : NeZero n] : SampleableType (ZMod n) where
  selectElem := (ZMod.finEquiv n) <$> ($ᵗ Fin n)
  mem_support_selectElem x := by
    rw [support_map]
    refine ⟨(ZMod.finEquiv n).symm x, ?_, by simp⟩
    simp
  probOutput_selectElem_eq x y := by
    calc
      Pr[= x | (ZMod.finEquiv n) <$> ($ᵗ Fin n)] =
          Pr[= (ZMod.finEquiv n).symm x | $ᵗ Fin n] := by
            simpa using
              (probOutput_map_injective ($ᵗ Fin n) (ZMod.finEquiv n).injective
                ((ZMod.finEquiv n).symm x))
      _ = Pr[= (ZMod.finEquiv n).symm y | $ᵗ Fin n] := by
            exact SampleableType.probOutput_selectElem_eq _ _
      _ = Pr[= y | (ZMod.finEquiv n) <$> ($ᵗ Fin n)] := by
            symm
            simpa using
              (probOutput_map_injective ($ᵗ Fin n) (ZMod.finEquiv n).injective
                ((ZMod.finEquiv n).symm y))

/-- Choose a random bit-vector by converting a random number between `0` and `2 ^ n`. -/
instance (n : ℕ) : SampleableType (BitVec n) where
  selectElem := BitVec.ofFin <$> ($ᵗ Fin (2 ^ n))
  mem_support_selectElem x := by aesop
  probOutput_selectElem_eq x y := by grind

/-- Select a uniform element from `Vector α n` by independently selecting `α` at each index. -/
instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := by induction n with
  | zero => exact pure #v[]
  | succ m ih => exact Vector.push <$> ih <*> ($ᵗ α)
  mem_support_selectElem x := by induction n with
  | zero => simp
  | succ m ih =>
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
  | succ m ih =>
    classical
    have hpush : Function.Injective2 (fun (xs : Vector α m) (x : α) => Vector.push xs x) := by
      intro xs ys x y hxy
      rcases Vector.push_eq_push.mp hxy with ⟨hxy', hxs⟩
      exact ⟨hxs, hxy'⟩
    rw [← Vector.push_pop_back x, ← Vector.push_pop_back y]
    rw [probOutput_seq_map_eq_mul_of_injective2 _ _ (fun (xs : Vector α m) (x : α) => Vector.push xs x)
      hpush x.pop x.back]
    rw [probOutput_seq_map_eq_mul_of_injective2 _ _ (fun (xs : Vector α m) (x : α) => Vector.push xs x)
      hpush y.pop y.back]
    have hback : Pr[= x.back | $ᵗ α] = Pr[= y.back | $ᵗ α] := by
      simpa [uniformSample] using
        (SampleableType.probOutput_selectElem_eq (β := α) x.back y.back)
    rw [hback]
    exact congrArg (fun z => z * Pr[= y.back | $ᵗ α]) (ih x.pop y.pop)

/-- A type equivalent to a `SampleableType` is also `SampleableType`. -/
def SampleableType.ofEquiv {α β : Type} [DecidableEq α] [DecidableEq β] [SampleableType α]
    (e : α ≃ β) : SampleableType β where
  selectElem := e <$> ($ᵗ α)
  mem_support_selectElem := fun x => by simp [support_map]
  probOutput_selectElem_eq := fun x y => by
    calc
      Pr[= x | e <$> ($ᵗ α)] = Pr[= e.symm x | ($ᵗ α)] := by
        simpa using probOutput_map_injective ($ᵗ α) e.injective (e.symm x)
      _ = Pr[= e.symm y | ($ᵗ α)] := by
        exact SampleableType.probOutput_selectElem_eq (e.symm x) (e.symm y)
      _ = Pr[= y | e <$> ($ᵗ α)] := by
        symm
        simpa using probOutput_map_injective ($ᵗ α) e.injective (e.symm y)

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

/-- Select a uniform element from `Matrix α n` by selecting each row independently. -/
instance (α : Type) (n m : ℕ) [SampleableType α] [DecidableEq α] :
    SampleableType (Matrix (Fin n) (Fin m) α) := by
  simpa [Matrix] using (inferInstance : SampleableType (Fin n → Fin m → α))

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
  simp [probOutput_bind_eq_tsum, add_comm]

/-- Conditioning on a uniform boolean averages the two branch probabilities. -/
lemma probOutput_bind_uniformBool {α : Type}
    (f : Bool → ProbComp α) (x : α) :
    Pr[= x | (do let b ← $ᵗ Bool; f b)] =
      (Pr[= x | f true] + Pr[= x | f false]) / 2 := by
  rw [probOutput_bind_eq_tsum]
  rw [tsum_fintype (L := .unconditional _), Fintype.sum_bool]
  simp [probOutput_uniformSample, div_eq_mul_inv, add_comm]
  rw [← left_distrib, mul_comm]

/-- Guessing a uniformly random bit after branching between `real` and `rand` decomposes into
the difference of the branch success probabilities. -/
lemma probOutput_uniformBool_branch_toReal_sub_half (real rand : ProbComp Bool) :
    (Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then real else rand
      pure (b == z)]).toReal - 1 / 2 =
    ((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2 := by
  have hgameRepr :
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then real else rand
        pure (b == z)] =
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] := by
    refine probOutput_bind_congr' ($ᵗ Bool) true ?_
    intro b
    cases b
    · have hbeqFalse : (BEq.beq false : Bool → Bool) = Bool.not := by
        funext t
        cases t <;> rfl
      simp [hbeqFalse]
    · have hbeqTrue : (BEq.beq true : Bool → Bool) = id := by
        funext t
        cases t <;> rfl
      simp [hbeqTrue]
  have hmix :
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] =
      (Pr[= true | (BEq.beq true <$> real)] + Pr[= true | (BEq.beq false <$> rand)]) / 2 :=
    probOutput_bind_uniformBool
      (f := fun b => if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand))
      (x := true)
  have hformula : Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then real else rand
      pure (b == z)] =
    (Pr[= true | real] + Pr[= false | rand]) / 2 := by
    rw [hgameRepr, hmix,
      show (BEq.beq true : Bool → Bool) = id from by ext b; cases b <;> rfl, id_map,
      show (BEq.beq false : Bool → Bool) = (! ·) from by ext b; cases b <;> rfl,
      probOutput_not_map]
  have hfalseAsSub : Pr[= false | rand] = 1 - Pr[= true | rand] := by
    have hsum : Pr[= true | rand] + Pr[= false | rand] = 1 := by simp
    rw [← hsum, ENNReal.add_sub_cancel_left probOutput_ne_top]
  rw [hformula, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    hfalseAsSub, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  simp [ENNReal.toReal_ofNat]
  ring

/-- If the distribution of `f b` is independent of `b`, then guessing a uniformly random
bit by running `f` has success probability exactly 1/2.
This is the core lemma behind "all-random hybrid has probability 1/2" arguments. -/
lemma probOutput_decide_eq_uniformBool_half
    (f : Bool → ProbComp Bool)
    (heq : evalDist (f true) = evalDist (f false)) :
    Pr[= true | do let b ← $ᵗ Bool; let b' ← f b; return decide (b = b')] = 1 / 2 := by
  have h := evalDist_ext_iff.mp heq
  rw [probOutput_bind_eq_tsum]
  simp only [tsum_fintype (L := .unconditional _), Fintype.sum_bool,
    probOutput_uniformSample, Fintype.card_bool]
  have htrue : Pr[= true | f true >>= fun b' => pure (decide (true = b'))] =
      Pr[= true | f true] := by
    rw [probOutput_bind_eq_tsum]; simp
  have hfalse : Pr[= true | f false >>= fun b' => pure (decide (false = b'))] =
      Pr[= false | f false] := by
    rw [probOutput_bind_eq_tsum]; simp
  have hsum : Pr[=true | f false] + Pr[=false | f false] = 1 := by
    have := HasEvalPMF.sum_probOutput_eq_one (f false)
    rwa [Fintype.sum_bool] at this
  rw [htrue, hfalse, h true, ← mul_add, hsum, mul_one]
  simp [one_div]
