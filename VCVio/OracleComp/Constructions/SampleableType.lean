/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.Bool
import VCVio.EvalDist.Prod
import VCVio.EvalDist.Fintype
import Init.Data.UInt.Lemmas
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector

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

notation:90 "$ᵗ " α:91 => uniformSample α

variable (α : Type) [hα : SampleableType α]

@[simp, grind =]
lemma probOutput_uniformSample [Fintype α] (x : α) :
    Pr[= x | $ᵗ α] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have : (Fintype.card α : ℝ≥0∞) = ∑ y : α, 1 :=
    by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  simp_rw [this, Finset.mul_sum, mul_one]
  rw [← sum_probOutput_eq_one (mx := $ᵗ α) (by aesop)]
  exact Finset.sum_congr rfl fun y _ ↦ SampleableType.probOutput_selectElem_eq x y

@[grind .]
lemma probOutput_uniformSample_inj (x y : α) : Pr[= x | $ᵗ α] = Pr[= y | $ᵗ α] :=
  SampleableType.probOutput_selectElem_eq _ _

lemma probOutput_map_bijective_uniformSample
    {f : α → α} (hf : Function.Bijective f) (x : α) :
    Pr[= x | f <$> ($ᵗ α)] = Pr[= x | $ᵗ α] := by
  obtain ⟨x', rfl⟩ := hf.surjective x
  rw [probOutput_map_injective ($ᵗ α) hf.injective x']
  exact SampleableType.probOutput_selectElem_eq _ _

/-- Pushing forward uniform sampling along a bijection preserves output probabilities. -/
lemma probOutput_map_bijective_uniform_cross
    {β : Type} [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (y : β) :
    Pr[= y | f <$> ($ᵗ α)] = Pr[= y | ($ᵗ β)] := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofBijective f hf
  obtain ⟨x, rfl⟩ := hf.surjective y
  rw [probOutput_map_injective ($ᵗ α) hf.injective x,
      probOutput_uniformSample, probOutput_uniformSample,
      Fintype.card_of_bijective hf]

/-- Binding after pushing forward uniform sampling along a bijection preserves output
probabilities. -/
lemma probOutput_bind_bijective_uniform_cross
    {β γ : Type} [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (g : β → ProbComp γ) (z : γ) :
    Pr[= z | ($ᵗ α) >>= fun x => g (f x)] =
      Pr[= z | ($ᵗ β) >>= fun y => g y] := by
  classical
  letI := Fintype.ofFinite α
  haveI := Fintype.ofBijective f hf
  have h : (($ᵗ α) >>= fun x => g (f x)) =
      ((f <$> ($ᵗ α)) >>= g) := by
    simp [monad_norm]
  rw [h, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1
  funext y
  congr 1
  exact probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf y

lemma probOutput_add_left_uniform [AddGroup α] (m x : α) :
    Pr[= x | (m + ·) <$> ($ᵗ α)] = Pr[= x | $ᵗ α] := by
  have h : Pr[= m + (-m + x) | ((m + ·) : α → α) <$> ($ᵗ α)] =
      Pr[= -m + x | $ᵗ α] :=
    probOutput_map_injective
      (mx := ($ᵗ α))
      (f := (m + ·))
      (hf := by intro a b hab; exact add_left_cancel hab)
      (x := -m + x)
  calc
    Pr[= x | ((m + ·) : α → α) <$> ($ᵗ α)]
        = Pr[= m + (-m + x) | ((m + ·) : α → α) <$> ($ᵗ α)] := by
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
      (do let y ← $ᵗ α; f (m + y)) =
        (((fun y : α => m + y) <$> ($ᵗ α)) >>= fun y => f y) := by
    simp [monad_norm]
  rw [hleft, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun y => ?_
  rw [probOutput_add_left_uniform (α := α) m y]

/-- Right-translation analogue of `probOutput_add_left_uniform`: right-adding a constant to a
uniform sample in `AddGroup α` preserves the output distribution, since `(· + m)` is a bijection
on `α` with inverse `(· + (-m))`. -/
lemma probOutput_add_right_uniform [AddGroup α] (m x : α) :
    Pr[= x | ((· + m) : α → α) <$> ($ᵗ α)] = Pr[= x | $ᵗ α] :=
  probOutput_map_bijective_uniformSample α (hf := AddGroup.addRight_bijective m) x

lemma probOutput_bind_add_right_uniform [AddGroup α] {β : Type}
    (m : α) (f : α → ProbComp β) (z : β) :
    Pr[= z | (do let y ← $ᵗ α; f (y + m))] =
      Pr[= z | (do let y ← $ᵗ α; f y)] := by
  have hright :
      (do let y ← $ᵗ α; f (y + m)) =
        (((fun y : α => y + m) <$> ($ᵗ α)) >>= fun y => f y) := by
    simp [monad_norm]
  rw [hright, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun y => ?_
  rw [probOutput_add_right_uniform (α := α) m y]

/-- Translating a uniform additive sample preserves the full evaluation distribution. -/
@[simp]
lemma evalDist_add_left_uniform [AddGroup α] (m : α) :
    𝒟[((m + ·) : α → α) <$> ($ᵗ α)] =
      𝒟[$ᵗ α] := by
  apply evalDist_ext
  intro x
  exact probOutput_add_left_uniform (α := α) m x

/-- Two additive translations of a uniform sample have the same evaluation distribution. -/
lemma evalDist_add_left_uniform_eq [AddGroup α] (m₁ m₂ : α) :
    𝒟[((m₁ + ·) : α → α) <$> ($ᵗ α)] =
      𝒟[((m₂ + ·) : α → α) <$> ($ᵗ α)] := by
  trans 𝒟[$ᵗ α]
  · exact evalDist_add_left_uniform (α := α) m₁
  · exact (evalDist_add_left_uniform (α := α) m₂).symm

/-- Right-translation analogue of `evalDist_add_left_uniform`: right-adding a constant to a
uniform sample in `AddGroup α` preserves the full evaluation distribution. -/
@[simp]
lemma evalDist_add_right_uniform [AddGroup α] (m : α) :
    𝒟[((· + m) : α → α) <$> ($ᵗ α)] =
      𝒟[$ᵗ α] := by
  apply evalDist_ext
  intro x
  exact probOutput_add_right_uniform (α := α) m x

/-- Two right-translations of a uniform sample have the same evaluation distribution. -/
lemma evalDist_add_right_uniform_eq [AddGroup α] (m₁ m₂ : α) :
    𝒟[((· + m₁) : α → α) <$> ($ᵗ α)] =
      𝒟[((· + m₂) : α → α) <$> ($ᵗ α)] := by
  trans 𝒟[$ᵗ α]
  · exact evalDist_add_right_uniform (α := α) m₁
  · exact (evalDist_add_right_uniform (α := α) m₂).symm

/-- Pushing forward uniform sampling via a bijection preserves the full evaluation distribution. -/
lemma evalDist_map_bijective_uniform_cross
    {β : Type} [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) :
    𝒟[f <$> ($ᵗ α)] = 𝒟[$ᵗ β] := by
  apply evalDist_ext
  intro y
  exact probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf y

/-- **Bijective uniform + right-translation gives uniform.** Sampling `x ← $ᵗ α`, transporting
through a bijection `f : α → β`, and right-adding any fixed `m : β` yields the same distribution
as sampling `y ← $ᵗ β` directly, as observed by any continuation `cont : β → ProbComp γ`.

This is the "one-time pad" fact underlying many cryptographic reductions: bijective transport
makes `f x` uniform on `β`, and in any `AddGroup β` right-translation `(· + m)` is a bijection
on the uniform measure, so the sum is again uniform. -/
lemma evalDist_bind_bijective_add_right_uniform {β γ : Type}
    [AddGroup β] [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (m : β) (cont : β → ProbComp γ) :
    𝒟[do let x ← ($ᵗ α); cont (f x + m)] =
      𝒟[do let y ← ($ᵗ β); cont y] := by
  have hbind :
      (do let x ← ($ᵗ α); cont (f x + m)) =
        (f <$> ($ᵗ α)) >>= fun y => cont (y + m) := by
    simp [monad_norm]
  rw [hbind, evalDist_bind,
      evalDist_map_bijective_uniform_cross (α := α) (β := β) f hf, ← evalDist_bind]
  have hshift :
      (do let y ← ($ᵗ β); cont (y + m)) =
        (((· + m) : β → β) <$> ($ᵗ β)) >>= cont := by
    simp [monad_norm]
  rw [hshift, evalDist_bind, evalDist_add_right_uniform (α := β) m, ← evalDist_bind]

/-- Constant-irrelevance form of `evalDist_bind_bijective_add_right_uniform`: sampling through a
bijection and right-adding a constant has a distribution independent of the constant. Any two
offsets produce the same evaluation distribution. -/
lemma evalDist_bind_bijective_add_right_eq {β γ : Type}
    [AddGroup β] [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (m₁ m₂ : β) (cont : β → ProbComp γ) :
    𝒟[do let x ← ($ᵗ α); cont (f x + m₁)] =
      𝒟[do let x ← ($ᵗ α); cont (f x + m₂)] := by
  rw [evalDist_bind_bijective_add_right_uniform (α := α) (β := β) f hf m₁ cont,
      ← evalDist_bind_bijective_add_right_uniform (α := α) (β := β) f hf m₂ cont]

lemma probFailure_uniformSample : Pr[⊥ | $ᵗ α] = 0 := by aesop

@[simp] instance : NeverFail ($ᵗ α) := inferInstance

@[simp, grind =]
lemma evalDist_uniformSample [Fintype α] [Nonempty α] :
    𝒟[$ᵗ α] = liftM (PMF.uniformOfFintype α) := by aesop

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
    Pr[ p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp only [probEvent_eq_sum_filter_univ, probOutput_uniformSample, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]

section instances

@[reducible] def SampleableType.Fin (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  mem_support_selectElem := by simp
  probOutput_selectElem_eq := by simp

instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) := by
  cases n with
  | zero => have := hn.out; contradiction
  | succ n => exact SampleableType.Fin n

instance (α : Type) [Unique α] : SampleableType α where
  selectElem := return default
  mem_support_selectElem x := Unique.eq_default x ▸ (by simp)
  probOutput_selectElem_eq x y := by rw [Unique.eq_default x, Unique.eq_default y]

instance : SampleableType Bool where
  selectElem := $! #v[true, false]
  mem_support_selectElem x := by simp
  probOutput_selectElem_eq x y := by simp

/-- A sum of oracle specs with sampleable ranges again has sampleable ranges. -/
instance {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    [h : ∀ t, SampleableType (spec.Range t)] [h' : ∀ t, SampleableType (spec'.Range t)] :
    ∀ t, SampleableType ((spec + spec').Range t)
  | .inl t => h t
  | .inr t => h' t

/-- Select a uniform element from `α × β` by independently selecting from `α` and `β`. -/
instance (α β : Type) [Fintype α] [Fintype β] [Inhabited α] [Inhabited β]
    [SampleableType α] [SampleableType β] : SampleableType (α × β) where
  selectElem := (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)
  mem_support_selectElem x := by simp
  probOutput_selectElem_eq x y := by simp

/-- A type equivalent to a `SampleableType` is also `SampleableType`. -/
@[reducible] def SampleableType.ofEquiv {α β : Type} [SampleableType α] (e : α ≃ β) :
    SampleableType β where
  selectElem := e <$> ($ᵗ α)
  mem_support_selectElem := fun x => by simp
  probOutput_selectElem_eq := fun x y => by grind

/-- Any finitely enumerable type can be sampled uniformly using the underlying equivalence. -/
instance FinEnum.SampleableType (α : Type)
    [h : FinEnum α] [Nonempty α] : SampleableType α := by
  have : NeZero (FinEnum.card α) := NeZero.mk FinEnum.card_ne_zero
  exact SampleableType.ofEquiv h.equiv.symm

/-- Noncomputable bridge from a nonempty `Fintype` with decidable equality to `SampleableType`,
via `Fintype.equivFin`. Used by downstream instances (e.g. `Sym α n`, `Equiv.Perm α`, `β ↪ α`)
whose Mathlib `Fintype` instances are not paired with a `FinEnum`. Provided as a `def` rather
than an `instance` to avoid overlap with `FinEnum.SampleableType`. -/
@[reducible] noncomputable def SampleableType.ofFintype (α : Type)
    [Fintype α] [Nonempty α] : SampleableType α :=
  haveI : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  SampleableType.ofEquiv (Fintype.equivFin α).symm

/-- This typeclass shouldn't cause diamonds since `Finite` is propositional. -/
instance SampleableType.Finite (α : Type) [SampleableType α] : Finite α :=
  Finite.of_finite_univ <| by simp only [← support_uniformSample, OracleComp.support_finite]

/-- We avoid making this an instance globally as many types already have a `Fintype` instance
that would not be definitionally equal to this one. -/
@[reducible]
noncomputable def SampleableType.Fintype (α : Type) [h : SampleableType α] [DecidableEq α] :
    Fintype α where
  elems := finSupport ($ᵗ α)
  complete := by grind

instance (n : ℕ) [NeZero n] : FinEnum (ZMod n) where
  card := n
  equiv := (ZMod.finEquiv n).symm.toEquiv

instance : FinEnum USize where
  card := 2 ^ System.Platform.numBits
  equiv := ⟨USize.toFin, USize.ofFin, fun x => by simp, fun x => by simp⟩

instance : FinEnum ISize where
  card := 2 ^ System.Platform.numBits
  equiv := ⟨BitVec.toFin ∘ ISize.toBitVec, ISize.ofBitVec ∘ BitVec.ofFin,
    fun x => by simp, fun x => by simp⟩

/-- Select a uniform element from `Vector α n` by independently selecting `α` at each index. -/
instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := by induction n with
  | zero => exact pure #v[]
  | succ m ih => exact Vector.push <$> ih <*> ($ᵗ α)
  mem_support_selectElem x := by induction n with
  | zero => simp
  | succ m ih =>
      have : ∃ ys y, Vector.push ys y = x := ⟨x.pop, x.back, Vector.push_pop_back x⟩
      simpa [ih] using this
  probOutput_selectElem_eq x y := by induction n with
  | zero => rw [show x = y by grind]
  | succ m ih =>
      have hpush : Function.Injective2 (Vector.push (α := α) (n := m)) := by
        intro xs ys x y hxy; simp [Vector.push_eq_push.mp hxy]
      simp only [Nat.recAux]
      rw [← Vector.push_pop_back x]
      rw [← Vector.push_pop_back y]
      erw [probOutput_seq_map_eq_mul_of_injective2 _ _ _ hpush x.pop x.back,
        probOutput_seq_map_eq_mul_of_injective2 _ _ _ hpush y.pop y.back,
        probOutput_uniformSample_inj, ih x.pop y.pop]

/-- `Vector α n` is finite when `α` is finite, via the equivalence with `Fin n → α`. -/
instance instFintypeVector (α : Type u) (n : ℕ) [Fintype α] : Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α)
    { toFun := Vector.ofFn
      invFun := fun v i => v.get i
      left_inv := fun f => funext fun i => by simp [Vector.get, Vector.ofFn]
      right_inv := fun v => Vector.ext fun i hi => by simp [Vector.ofFn, Vector.get] }

/-- A function from `Fin n` to a `SampleableType` is also `SampleableType`. This is the base
case used by the general `FinEnum`-indexed `instSampleableTypeFunc` below. -/
instance instSampleableTypeFinFunc {n : ℕ} {α : Type} [SampleableType α] :
    SampleableType (Fin n → α) :=
  SampleableType.ofEquiv
    { toFun := fun v i => v.get i
      invFun := Vector.ofFn
      left_inv := fun v => Vector.ext fun i hi => by simp [Vector.ofFn, Vector.get]
      right_inv := fun f => funext fun i => by simp [Vector.get, Vector.ofFn] }

/-- A function `β → α` for `β` finitely enumerable and `α` sampleable is itself sampleable.
This generalizes the `Fin n → α` instance above: the `FinEnum.fin` instance recovers it. -/
instance instSampleableTypeFunc {β α : Type} [FinEnum β] [SampleableType α] :
    SampleableType (β → α) :=
  SampleableType.ofEquiv (α := Fin (FinEnum.card β) → α)
    (Equiv.arrowCongr FinEnum.equiv.symm (Equiv.refl α))

/-- Select a uniform element from `List.Vector α n` by independently selecting `α` at each
index. The construction goes through the equivalence with `Fin n → α`. -/
instance instSampleableTypeListVector {α : Type} {n : ℕ} [SampleableType α] :
    SampleableType (List.Vector α n) :=
  SampleableType.ofEquiv
    { toFun := List.Vector.ofFn
      invFun := fun xs i => xs.get i
      left_inv := fun f => funext fun i => by simp
      right_inv := fun xs => List.Vector.ext fun i => by simp }

/-- Select a uniform element from `Matrix ι κ α` by independently selecting an entry for each
`(i, j)`. Both index types only need to be `FinEnum`; the previous `Fin n × Fin m`-indexed
instance is recovered through `FinEnum.fin`. -/
instance instSampleableTypeMatrix {α ι κ : Type} [FinEnum ι] [FinEnum κ] [SampleableType α] :
    SampleableType (Matrix ι κ α) :=
  inferInstanceAs (SampleableType (ι → κ → α))

/-- Discoverability wrapper: `SampleableType (α ⊕ β)` follows from `FinEnum` on each side
plus nonemptiness of the sum, via Mathlib's `FinEnum.sum` instance and
`FinEnum.SampleableType`. Listed explicitly so users can see it in the instance set rather
than relying on a multi-step search. -/
instance instSampleableTypeSum {α β : Type} [FinEnum α] [FinEnum β]
    [Nonempty (α ⊕ β)] : SampleableType (α ⊕ β) :=
  inferInstance

/-- Discoverability wrapper: `SampleableType (Finset α)` for `FinEnum α`. Uniform sampling
draws every subset of `α` with the same probability (`2^|α|` outcomes). `Finset α` is always
inhabited by `∅`, so no `Nonempty` hypothesis is needed. -/
instance instSampleableTypeFinset {α : Type} [FinEnum α] : SampleableType (Finset α) :=
  inferInstance

/-- Uniform sampling of size-`n` multisets over `α`. `Sym α n` is the correct finite analogue
of `Multiset α`: a plain `Multiset α` is unbounded in multiplicity and thus not `Fintype`,
while `Sym α n` is a `Fintype` whenever `α` is. The `Mathlib` instance lives in
`Mathlib.Data.Fintype.Vector`; we lift it through `SampleableType.ofFintype`. -/
noncomputable instance instSampleableTypeSym {α : Type} {n : ℕ}
    [Fintype α] [DecidableEq α] [Nonempty α] : SampleableType (Sym α n) :=
  haveI : Nonempty (Sym α n) := ⟨.replicate n (Classical.arbitrary α)⟩
  SampleableType.ofFintype _

/-- Uniform sampling of permutations of a finite type. `Equiv.Perm α` has `n!` elements when
`Fintype.card α = n`. Mathlib provides `Fintype (Equiv.Perm α)` via
`Mathlib.Data.Fintype.Perm`; we lift through `SampleableType.ofFintype`. Useful for
shuffle-based protocols and oblivious-permutation games. -/
noncomputable instance instSampleableTypePerm {α : Type} [Fintype α] [DecidableEq α] :
    SampleableType (Equiv.Perm α) :=
  haveI : Nonempty (Equiv.Perm α) := ⟨Equiv.refl α⟩
  SampleableType.ofFintype _

/-- Uniform sampling of injections `β ↪ α` for finite types. The number of such embeddings is
`α.card! / (α.card - β.card)!` when `β.card ≤ α.card`, else `0`; the `Nonempty (β ↪ α)`
hypothesis rules out the latter case. Mathlib provides `Fintype (β ↪ α)` via
`Mathlib.Data.Fintype.Pi`; we lift through `SampleableType.ofFintype`. -/
noncomputable instance instSampleableTypeEmbedding {β α : Type}
    [Fintype β] [Fintype α] [DecidableEq β] [DecidableEq α] [Nonempty (β ↪ α)] :
    SampleableType (β ↪ α) :=
  SampleableType.ofFintype _

/-- A function from a finite type `D` with decidable equality to a `SampleableType` is itself
`SampleableType`: transport the `Fin (Fintype.card D) → α` instance across the canonical
equivalence `(D → α) ≃ (Fin (Fintype.card D) → α)`. This is the general Pi instance over an
arbitrary finite domain presented by `Fintype` + `DecidableEq`, complementing the `FinEnum`-domain
instance `instSampleableTypeFunc`. -/
noncomputable instance instSampleableTypePiFintype {D : Type} [Fintype D] [DecidableEq D]
    {α : Type} [SampleableType α] : SampleableType (D → α) :=
  SampleableType.ofEquiv
    (α := Fin (Fintype.card D) → α)
    (Equiv.arrowCongr (Fintype.equivFin D).symm (Equiv.refl α))

end instances

section Marginalization

/-- **Overwriting one coordinate of a uniform function table is measure-preserving.**

Drawing a value `u` uniformly from `R`, then a full function table `g : D → R` uniformly, and
returning `Function.update g t u` yields the same distribution as drawing the table directly.

This is the `t`-marginal independence of the uniform (product) distribution on `D → R`: the value
at coordinate `t` is uniform and independent of the others, so replacing it with a fresh
independent uniform draw leaves the joint distribution unchanged. It is the marginalization step
behind eager-sampling reformulations of oracle responses. -/
lemma evalDist_uniformSample_bind_update
    {D R : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) :
    𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u)] =
      𝒟[$ᵗ (D → R)] := by
  classical
  letI := Fintype.ofFinite D
  letI := Fintype.ofFinite R
  haveI : Nonempty (D → R) := ⟨fun _ => Classical.arbitrary R⟩
  refine evalDist_ext fun h => ?_
  rw [probOutput_uniformSample (D → R) h, probOutput_bind_eq_sum_fintype]
  -- For each fixed `u`, count the tables `g` whose `t`-update equals `h`.
  have hinner : ∀ u : R,
      Pr[= h | (do let g ← $ᵗ (D → R); pure (Function.update g t u))]
        = (if u = h t then
            (Fintype.card R : ℝ≥0∞) * (Fintype.card (D → R) : ℝ≥0∞)⁻¹ else 0) := by
    intro u
    have hmap : (do let g ← $ᵗ (D → R); pure (Function.update g t u))
        = (fun g => Function.update g t u) <$> ($ᵗ (D → R)) := by
      rw [bind_pure_comp]
    rw [hmap, probOutput_map_eq_sum_fintype_ite]
    simp only [probOutput_uniformSample (D → R)]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    -- The matching tables are exactly `Function.update h t r` for `r : R`.
    have hcard :
        ((Finset.univ.filter fun g : D → R => h = Function.update g t u).card : ℝ≥0∞)
          = if u = h t then (Fintype.card R : ℝ≥0∞) else 0 := by
      by_cases hu : u = h t
      · have hset : (Finset.univ.filter fun g : D → R => h = Function.update g t u)
            = Finset.univ.image (fun r : R => Function.update h t r) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hg
            refine ⟨g t, ?_⟩
            rw [eq_comm, Function.update_eq_iff] at hg
            obtain ⟨_, hg2⟩ := hg
            funext x
            by_cases hx : x = t
            · subst hx; simp
            · simp [Function.update_of_ne hx, hg2 x hx]
          · rintro ⟨r, rfl⟩
            rw [eq_comm, Function.update_eq_iff]
            exact ⟨by simp [hu], fun x hx => by simp [Function.update_of_ne hx]⟩
        rw [hset, Finset.card_image_of_injective _
          (fun r₁ r₂ hr => by simpa using congrFun hr t), Finset.card_univ, if_pos hu]
      · have hempty : (Finset.univ.filter fun g : D → R => h = Function.update g t u) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro g _ hg
          rw [eq_comm, Function.update_eq_iff] at hg
          exact hu hg.1
        rw [hempty, Finset.card_empty, Nat.cast_zero, if_neg hu]
    rw [hcard]
    by_cases hu : u = h t <;> simp [hu]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (h t)]
  rw [if_pos (Finset.mem_univ _), probOutput_uniformSample R, ← mul_assoc,
      ENNReal.inv_mul_cancel, one_mul]
  · simp [Fintype.card_ne_zero]
  · exact ENNReal.natCast_ne_top _

/-- **The first coordinate of a uniform pair is uniform.**

Mapping the uniform distribution on `α × β` through `Prod.fst` yields the uniform distribution on
`α`: the `Prod.fst`-marginal of a uniform (product) distribution is uniform. -/
lemma evalDist_map_fst_uniformSample_prod {α β : Type} [Finite α]
    [Finite β] [Nonempty β] [SampleableType α] [SampleableType β] [SampleableType (α × β)] :
    𝒟[Prod.fst <$> ($ᵗ (α × β))] = 𝒟[$ᵗ α] := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  haveI : DecidableEq α := Classical.decEq α
  refine evalDist_ext fun x => ?_
  rw [probOutput_uniformSample α x, probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample (α × β)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hset : (Finset.univ.filter fun p : α × β => x = p.1)
      = ({x} : Finset α) ×ˢ (Finset.univ : Finset β) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
    exact eq_comm
  rw [hset, Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc, mul_comm (Fintype.card β : ℝ≥0∞) (Fintype.card α : ℝ≥0∞)⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), mul_one]

/-- **Restricting a uniform function table to a subdomain along an injection is uniform.**

For an injection `e : A → B` between finite types, drawing a uniform table `g : B → R` and
restricting it along `e` (i.e. `g ∘ e`) yields the uniform distribution on `A → R`.

This is the marginalization of the uniform (product) distribution on `B → R` onto the block of
coordinates indexed by `Set.range e`: those coordinates are jointly uniform and independent of
the rest, and `e` reindexes the block by `A`. It underlies eager-sampling reformulations that
project a fine-grained random-oracle table onto a coarser one. -/
lemma evalDist_uniformSample_map_comp_injective
    {A B R : Type} [Finite A] [Finite B] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (A → R)] [SampleableType (B → R)]
    {e : A → B} (he : Function.Injective e) :
    𝒟[do let g ← $ᵗ (B → R); pure (g ∘ e)] = 𝒟[$ᵗ (A → R)] := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite R
  haveI : DecidableEq A := Classical.decEq A
  haveI : DecidableEq B := Classical.decEq B
  letI : Inhabited R := Classical.inhabited_of_nonempty inferInstance
  set C := {b : B // b ∉ Set.range e} with hC
  letI : Fintype C := Fintype.ofFinite C
  letI : Inhabited (A → R) := ⟨fun _ => default⟩
  letI : Inhabited (C → R) := ⟨fun _ => default⟩
  haveI : DecidableEq C := Classical.decEq C
  letI : FinEnum C := FinEnum.ofEquiv _ (Fintype.equivFin C)
  haveI hsC : SampleableType (C → R) := inferInstance
  haveI hsP : SampleableType ((A → R) × (C → R)) := inferInstance
  -- Split `B → R` into the `range e` block (reindexed by `A`) and its complement `C`:
  -- a table is determined by its restriction along `e` and its values off `range e`.
  set φ : (B → R) ≃ (A → R) × (C → R) :=
    { toFun := fun g => (g ∘ e, fun c => g c.1)
      invFun := fun p b => if h : ∃ a, e a = b then p.1 h.choose else p.2 ⟨b, by
        simpa [Set.mem_range] using h⟩
      left_inv := fun g => by
        funext b
        by_cases h : ∃ a, e a = b
        · simp only [h, dif_pos, Function.comp_apply]
          exact congrArg g h.choose_spec
        · simp [h]
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext a
          have h : ∃ a', e a' = e a := ⟨a, rfl⟩
          simp only [Function.comp_apply, h, dif_pos]
          exact congrArg p.1 (he h.choose_spec)
        · funext c
          have h : ¬ ∃ a, e a = c.1 := by simpa [Set.mem_range] using c.2
          simp only [h, dif_neg, not_false_iff]
          exact congrArg p.2 (Subtype.ext rfl) }
    with hφ
  have hφ1 : ∀ g : B → R, (φ g).1 = g ∘ e := fun g => rfl
  have hmap : (do let g ← $ᵗ (B → R); pure (g ∘ e)) = (Prod.fst ∘ φ) <$> ($ᵗ (B → R)) := by
    rw [bind_pure_comp]; exact congrArg (· <$> _) (funext fun g => (hφ1 g).symm)
  have hcross : 𝒟[φ <$> ($ᵗ (B → R))] = 𝒟[$ᵗ ((A → R) × (C → R))] :=
    evalDist_ext fun p =>
      probOutput_map_bijective_uniform_cross (α := B → R) φ φ.bijective p
  calc 𝒟[do let g ← $ᵗ (B → R); pure (g ∘ e)]
      = 𝒟[(Prod.fst ∘ φ) <$> ($ᵗ (B → R))] := by rw [hmap]
    _ = 𝒟[Prod.fst <$> (φ <$> ($ᵗ (B → R)))] := by
        simp only [Functor.map_map, Function.comp_def]
    _ = 𝒟[Prod.fst <$> ($ᵗ ((A → R) × (C → R)))] := by
        rw [evalDist_map, hcross, ← evalDist_map]
    _ = 𝒟[$ᵗ (A → R)] := evalDist_map_fst_uniformSample_prod

/-- Patch a uniform function table at every point of a list `l`, drawing one fresh uniform value
per list entry. With `l = []` the table is returned unchanged; with `l = d :: ds` the tail is
patched first and the head point `d` is then overwritten with a fresh uniform draw.

This is the iterated form of `Function.update` used by `evalDist_uniformSample_patchList`: the
outermost update is at the head, so the list is consumed head-first. -/
noncomputable def patchTable {D R : Type} [DecidableEq D] [SampleableType R] :
    List D → (D → R) → ProbComp (D → R)
  | [], g => pure g
  | d :: ds, g => do
      let g' ← patchTable ds g
      let u ← $ᵗ R
      pure (Function.update g' d u)

@[simp] lemma patchTable_nil {D R : Type} [DecidableEq D] [SampleableType R] (g : D → R) :
    patchTable [] g = pure g := rfl

lemma patchTable_cons {D R : Type} [DecidableEq D] [SampleableType R]
    (d : D) (ds : List D) (g : D → R) :
    patchTable (d :: ds) g =
      (do let g' ← patchTable ds g; let u ← $ᵗ R; pure (Function.update g' d u)) := rfl

/-- **Patching a uniform function table at finitely many points preserves uniformity.**

Drawing a uniform table `g : D → R` and then `patchTable l g` — overwriting `g` at every point of
`l` with independent fresh uniform draws — yields the same distribution as drawing the table
directly. The points of `l` need not be distinct: each `Function.update` is the outermost
operation of its recursion step, so `evalDist_uniformSample_bind_update` applies regardless of
overlap. This is the marginalization step behind trace-conditioned eager-table reformulations,
where the patched points are determined only after the table is sampled. -/
lemma evalDist_uniformSample_patchList
    {D R : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (l : List D) :
    𝒟[do let g ← $ᵗ (D → R); patchTable l g] = 𝒟[$ᵗ (D → R)] := by
  classical
  induction l with
  | nil => simp [patchTable_nil, bind_pure]
  | cons d ds ih =>
    refine evalDist_ext fun h => ?_
    -- The tail-patch block, abbreviated.
    set blk : ProbComp (D → R) := (do let g ← $ᵗ (D → R); patchTable ds g) with hblk
    -- LHS: unfold one `patchTable` step and reassociate so the tail-patch block stands alone.
    have hlhs :
        Pr[= h | do let g ← $ᵗ (D → R); patchTable (d :: ds) g]
          = Pr[= h | blk >>= fun g' => $ᵗ R >>= fun u => pure (Function.update g' d u)] := by
      refine OracleComp.probOutput_congr rfl ?_
      simp only [patchTable_cons, bind_assoc, hblk]
    rw [hlhs]
    -- Push the tail-patch block through the bind; by the IH it is the uniform table.
    rw [probOutput_bind_eq_tsum]
    have hihp : ∀ g' : D → R, Pr[= g' | blk] = Pr[= g' | $ᵗ (D → R)] :=
      fun g' => OracleComp.probOutput_congr rfl ih
    simp_rw [hihp]
    rw [← probOutput_bind_eq_tsum]
    -- Now swap the table draw and the fresh-uniform draw, then apply the single-cell lemma.
    rw [probOutput_bind_bind_swap ($ᵗ (D → R)) ($ᵗ R)
      (fun g' u => pure (Function.update g' d u))]
    exact OracleComp.probOutput_congr rfl (evalDist_uniformSample_bind_update d)

end Marginalization

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
  simp only [probOutput_uniformSample, Fintype.card_bool, Nat.cast_ofNat, add_comm, div_eq_mul_inv]
  rw [← left_distrib, mul_comm]

/-- Guessing a uniformly random bit after branching between `real` and `rand` decomposes into
the difference of the branch success probabilities. -/
lemma probOutput_uniformBool_branch_toReal_sub_half (real rand : ProbComp Bool) :
    (Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)]).toReal - 1 / 2 =
    ((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2 := by
  have hgameRepr :
      Pr[= true | do
        let b ← ($ᵗ Bool)
        let z ← if b then real else rand
        pure (b == z)] =
      Pr[= true | do
        let b ← ($ᵗ Bool)
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
        let b ← ($ᵗ Bool)
        if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand)] =
      (Pr[= true | (BEq.beq true <$> real)] + Pr[= true | (BEq.beq false <$> rand)]) / 2 :=
    probOutput_bind_uniformBool
      (f := fun b => if b then (BEq.beq true <$> real) else (BEq.beq false <$> rand))
      (x := true)
  have hformula : Pr[= true | do
      let b ← ($ᵗ Bool)
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
    (heq : 𝒟[f true] = 𝒟[f false]) :
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
  have hsum : Pr[= true | f false] + Pr[= false | f false] = 1 := by
    have := sum_probOutput_of_liftM_PMF (f false)
    rwa [Fintype.sum_bool] at this
  rw [htrue, hfalse, h true, ← mul_add, hsum, mul_one]
  simp [one_div]

section UniformSampleImpl

open OracleSpec OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

/-- Given that the output type of all oracles has a `SampleableType` instance, replace all queries
with uniformly random responses by calling the corresponding `uniformSample` at each query. -/
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t

namespace uniformSampleImpl

variable [∀ i, SampleableType (spec.Range i)]

@[simp]
lemma evalDist_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) :
    𝒟[simulateQ uniformSampleImpl oa] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h, uniformSampleImpl]

@[simp]
lemma probOutput_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | simulateQ uniformSampleImpl oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ oa)) x

@[simp]
lemma probEvent_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[ p | simulateQ uniformSampleImpl oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_simulateQ]

@[simp]
lemma support_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) :
    support (simulateQ uniformSampleImpl oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h, uniformSampleImpl]

@[simp]
lemma finSupport_simulateQ [IsUniformSpec spec] {α : Type}
    [DecidableEq α] (oa : OracleComp spec α) :
    finSupport (simulateQ uniformSampleImpl oa) = finSupport oa := by
  simp [finSupport_eq_iff_support_eq_coe]

end uniformSampleImpl

end UniformSampleImpl
