/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.NNRat.BigOperators

/-!
# Probability mass functions with finite support and non-negative rational weights

This is a special case of `PMF` that suffices for denotational semantics of `OracleComp` with finite
oracle specifications.

## Design

We use a two-layer approach:

* `FinRatPMF.Raw α` is a list-based representation storing pairs `(a, p)` of outcomes and
  probabilities. It has a computable `Monad` and `LawfulMonad` instance but non-canonical equality:
  two values representing the same distribution may differ in list order or duplicate entries.

* `FinRatPMF α` is the quotient of `FinRatPMF.Raw α` by distributional equality (`SameDist`).
  It has canonical equality (two values are equal iff they define the same distribution) and a
  `LawfulMonad` instance (necessarily `noncomputable` since `bind` must extract from the quotient).

For computation, use `FinRatPMF.Raw`. For reasoning about distributional equality, use `FinRatPMF`.
Both connect to Mathlib's `PMF` via `toPMF`.
-/

@[expose] public section

universe u

namespace FinRatPMF

/-! ## Raw representation -/

/-- Raw probability mass function with finite support and non-negative rational weights.

Stores a list of `(outcome, weight)` pairs whose weights sum to `1`. This representation is
computable but not canonical: many different `FinRatPMF.Raw` values can represent the same
probability distribution. -/
structure Raw (α : Type u) : Type u where
  toList : List (α × ℚ≥0)
  sum_eq_one : (toList.map Prod.snd).sum = 1

namespace Raw

variable {α β γ : Type u}

@[ext] lemma ext {p q : Raw α} (h : p.toList = q.toList) : p = q := by
  cases p; cases q; congr

/-! ### Bind sum auxiliary lemma -/

private lemma bind_sum_aux (l : List (α × ℚ≥0)) (g : α → Raw β) :
    ((l.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q)))).map Prod.snd).sum
    = (l.map (fun (a, p) => p * ((g a).toList.map Prod.snd).sum)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_map, Function.comp_def]
    rw [List.sum_map_mul_left]; congr 1

/-! ### Monad operations -/

protected def pure (a : α) : Raw α := ⟨[(a, 1)], by simp⟩

protected def bind (f : Raw α) (g : α → Raw β) : Raw β :=
  ⟨f.toList.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q))), by
    rw [bind_sum_aux]
    simp_rw [Raw.sum_eq_one, mul_one]
    exact f.sum_eq_one⟩

instance : Monad Raw where
  pure := Raw.pure
  bind := Raw.bind

@[simp] lemma pure_toList (a : α) :
    (Pure.pure a : Raw α).toList = [(a, 1)] := rfl

@[simp] lemma bind_toList (f : Raw α) (g : α → Raw β) :
    (f >>= g).toList =
      f.toList.flatMap (fun (a, p) => (g a).toList.map (fun (b, q) => (b, p * q))) := rfl

instance : LawfulMonad Raw := LawfulMonad.mk'
  (id_map := fun x => by ext; simp [Functor.map, Raw.bind, Raw.pure])
  (pure_bind := fun x f => by ext; simp)
  (bind_assoc := fun m f g => by
    ext; simp [List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def, mul_assoc])
  (bind_pure_comp := fun f x => by
    ext; simp [Functor.map, Raw.bind, Raw.pure])

/-! ### Probability and support -/

/-- The probability assigned to `x` by the raw PMF: sum of weights for all entries with key `x`. -/
def prob [DecidableEq α] (p : Raw α) (x : α) : ℚ≥0 :=
  (p.toList.filter (fun a => a.1 = x) |>.map Prod.snd).sum

/-- `prob` is independent of the `DecidableEq` instance, since `decide (a = b)` gives the same
`Bool` for any `Decidable` instance on the same `Prop`. -/
lemma prob_eq_prob (inst1 inst2 : DecidableEq α) (p : Raw α) (x : α) :
    @prob _ inst1 p x = @prob _ inst2 p x := by
  unfold prob; congr 2
  apply List.filter_congr
  intro a _
  show @decide (a.1 = x) (inst1 a.1 x) = @decide (a.1 = x) (inst2 a.1 x)
  cases inst1 a.1 x <;> cases inst2 a.1 x <;> simp_all

/-- The finite support: the set of outcomes appearing in the list. -/
def support [DecidableEq α] (p : Raw α) : Finset α :=
  p.toList.map Prod.fst |>.toFinset

lemma prob_eq_zero_of_not_mem_support [DecidableEq α] (p : Raw α) {x : α}
    (hx : x ∉ p.support) : p.prob x = 0 := by
  simp only [prob, support, List.mem_toFinset, List.mem_map] at hx ⊢
  suffices p.toList.filter (fun a => a.1 = x) = [] by simp [this]
  rw [List.filter_eq_nil_iff]
  intro a ha
  simp only [decide_eq_true_eq]
  intro heq
  exact hx ⟨a, ha, heq ▸ rfl⟩

private lemma filter_cons_sum [DecidableEq α] (hd : α × ℚ≥0) (tl : List (α × ℚ≥0)) (x : α) :
    ((hd :: tl).filter (fun a => a.1 = x) |>.map Prod.snd).sum =
    (if hd.1 = x then hd.2 else 0) +
    (tl.filter (fun a => a.1 = x) |>.map Prod.snd).sum := by
  simp only [List.filter_cons, decide_eq_true_eq]
  split <;> simp_all [List.map_cons, List.sum_cons]

private lemma list_prob_eq_zero [DecidableEq α] {l : List (α × ℚ≥0)} {x : α}
    (hx : x ∉ (l.map Prod.fst).toFinset) :
    (l.filter (fun a => a.1 = x) |>.map Prod.snd).sum = 0 := by
  suffices l.filter (fun a => a.1 = x) = [] by simp [this]
  rw [List.filter_eq_nil_iff]
  simp only [List.mem_toFinset, List.mem_map] at hx
  exact fun a ha => by simp; intro heq; exact hx ⟨a, ha, heq ▸ rfl⟩

private lemma list_sum_prob_eq [DecidableEq α] (l : List (α × ℚ≥0)) :
    (l.map Prod.fst |>.toFinset).sum
      (fun x => (l.filter (fun a => a.1 = x) |>.map Prod.snd).sum) =
    (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.toFinset_cons, List.sum_cons]
    simp_rw [filter_cons_sum, Finset.sum_add_distrib]
    congr 1
    · simp
    · by_cases hm : hd.1 ∈ (tl.map Prod.fst).toFinset
      · rw [Finset.insert_eq_of_mem hm]; exact ih
      · rw [Finset.sum_insert hm, list_prob_eq_zero hm, zero_add]; exact ih

/-- Sum of `prob` over the support recovers the total weight. -/
lemma sum_prob_eq_sum [DecidableEq α] (p : Raw α) :
    p.support.sum p.prob = (p.toList.map Prod.snd).sum :=
  list_sum_prob_eq p.toList

/-- Convert to a `PMF` by mapping weights through `ℚ≥0 → ℝ≥0 → ℝ≥0∞`. -/
noncomputable def toPMF [DecidableEq α] (p : Raw α) : PMF α :=
  PMF.ofFinset (fun x => ((p.prob x : NNReal) : ENNReal)) p.support
    (by
      rw [← ENNReal.coe_finset_sum, ← NNRat.cast_sum (K := NNReal)]
      simp [sum_prob_eq_sum, p.sum_eq_one])
    (fun a ha => by simp [prob_eq_zero_of_not_mem_support p ha])

end Raw

/-! ## Distributional equality and quotient -/

variable {α β γ : Type u}

/-- Two raw PMFs represent the same distribution if they assign the same probability to every
outcome. Uses classical decidable equality since this is a `Prop`. -/
def SameDist (p q : Raw α) : Prop :=
  ∀ x : α, @Raw.prob _ (Classical.decEq _) p x =
            @Raw.prob _ (Classical.decEq _) q x

lemma SameDist.refl (p : Raw α) : SameDist p p := fun _ => rfl

lemma SameDist.symm {p q : Raw α} (h : SameDist p q) : SameDist q p :=
  fun x => (h x).symm

lemma SameDist.trans {p q r : Raw α} (hpq : SameDist p q) (hqr : SameDist q r) :
    SameDist p r :=
  fun x => (hpq x).trans (hqr x)

instance : IsEquiv (Raw α) SameDist where
  refl := SameDist.refl
  symm := @SameDist.symm _
  trans := @SameDist.trans _

instance Raw.instSetoid : Setoid (Raw α) where
  r := SameDist
  iseqv := ⟨SameDist.refl, SameDist.symm, SameDist.trans⟩

end FinRatPMF

/-- Probability mass function with finite support and rational weights, with canonical equality.

Defined as the quotient of `FinRatPMF.Raw` by distributional equality. Two values are equal iff
they assign the same probability to every outcome. -/
def FinRatPMF (α : Type u) : Type u := Quotient (α := FinRatPMF.Raw α) inferInstance

namespace FinRatPMF

variable {α β γ : Type u}

/-- Construct from a raw PMF. -/
def mk (p : Raw α) : FinRatPMF α := Quotient.mk _ p

/-- `FinRatPMF` equality is distributional equality. -/
lemma eq_iff {p q : Raw α} : mk p = mk q ↔ SameDist p q :=
  Quotient.eq

/-! ### Monad operations -/

/-- The `bind` of the quotient needs to extract from the Kleisli function's codomain, which is
itself a quotient. This requires `Quot.out` and is therefore noncomputable. -/
noncomputable instance : Monad FinRatPMF where
  pure a := mk (Raw.pure a)
  bind ma f := mk (Raw.bind (Quotient.out ma) (fun a => Quotient.out (f a)))

/-! ### Connection to `PMF` -/

/-- Convert a `FinRatPMF` to a `PMF`. Well-defined since `SameDist` implies equal `toPMF`. -/
noncomputable def toPMF [DecidableEq α] (p : FinRatPMF α) : PMF α :=
  Quotient.lift (fun raw => raw.toPMF) (by
    intro a b hab
    ext x
    simp only [Raw.toPMF, PMF.ofFinset_apply]
    have key := hab x
    rw [Raw.prob_eq_prob (Classical.decEq _) _ a x,
        Raw.prob_eq_prob (Classical.decEq _) _ b x] at key
    exact_mod_cast key) p

lemma toPMF_injective [DecidableEq α] : Function.Injective (toPMF (α := α)) := by
  intro p q hpq
  induction p using Quotient.inductionOn with | _ a => ?_
  induction q using Quotient.inductionOn with | _ b => ?_
  rw [Quotient.eq]
  intro x
  have key : (a.toPMF : PMF α) x = (b.toPMF : PMF α) x := by
    have := congr_fun (congr_arg DFunLike.coe hpq) x
    simpa [toPMF, Quotient.lift_mk]
  simp only [Raw.toPMF, PMF.ofFinset_apply] at key
  calc @Raw.prob _ (Classical.decEq _) a x
      = a.prob x := Raw.prob_eq_prob _ _ _ _
    _ = b.prob x := by exact_mod_cast key
    _ = @Raw.prob _ (Classical.decEq _) b x :=
        (Raw.prob_eq_prob _ _ _ _).symm

end FinRatPMF
