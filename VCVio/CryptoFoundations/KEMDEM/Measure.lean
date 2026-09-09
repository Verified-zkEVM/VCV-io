/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Measure
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Measure-based KEM–DEM hybrid argument

The computations take a preparation phase, encapsulation, and a final observation.
They preserve the original effect order. Probability enters only through a lawful
measure interpretation, a fair coin, a lossless independent key, and total hybrid
outputs. The KEM identity is shared by both message branches.
-/

public section

open MeasureTheory

namespace KEMDEM
variable {m : Type → Type*} [Monad m]
  {A B K : Type}
/-- Run one message branch using either the encapsulated key or an independent key. -/
@[expose]
def hybrid (prepare : m A) (encaps : A → m (B × K))
    (finish : A → B → K → Bool → m Bool) (key : m K) (real side : Bool) : m Bool := do
  let a ← prepare
  let (c, k) ← encaps a
  let k' ← if real then pure k else key
  finish a c k' side

/-- The KEM guessing experiment for one fixed message branch. -/
@[expose]
def kemGame (prepare : m A) (encaps : A → m (B × K))
    (finish : A → B → K → Bool → m Bool) (coin : m Bool) (key : m K)
    (side : Bool) : m Bool := do
  let a ← prepare
  let b ← coin
  let (c, k) ← encaps a
  let kr ← key
  let z ← finish a c (if b then k else kr) side
  pure (b == z)

/-- The composed encryption guessing experiment, with its challenge bit sampled first. -/
@[expose]
def composedGame (prepare : m A) (encaps : A → m (B × K))
    (finish : A → B → K → Bool → m Bool) (coin : m Bool) : m Bool := do
  let b ← coin
  let a ← prepare
  let (c, k) ← encaps a
  let z ← finish a c k b
  pure (b == z)

/-- The DEM guessing experiment, with the independent key sampled before preparation. -/
@[expose]
def demGame (prepare : m A) (encaps : A → m (B × K))
    (finish : A → B → K → Bool → m Bool) (coin : m Bool) (key : m K) : m Bool := do
  let b ← coin
  let kr ← key
  let a ← prepare
  let (c, _) ← encaps a
  let z ← finish a c kr (!b)
  pure (b == z)

/-- The composed experiment is a hidden-bit choice between its two real-key branches. -/
lemma composedGame_eq [LawfulMonad m]
    (prepare : m A) (encaps : A → m (B × K))
    (finish : A → B → K → Bool → m Bool) (coin : m Bool) (key : m K) :
    composedGame prepare encaps finish coin =
    (coin >>= fun b => (if b then hybrid prepare encaps finish key true true
      else hybrid prepare encaps finish key true false) >>= fun z => pure (b == z)) := by
  apply bind_congr
  intro b
  cases b <;> simp [hybrid]

variable [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace (B × K)] [DiscreteMeasurableSpace (B × K)]
  [MeasurableSpace K] [DiscreteMeasurableSpace K] [Countable K]
  (prepare : m A) (encaps : A → m (B × K))
  (finish : A → B → K → Bool → m Bool) (coin : m Bool) (key : m K)

omit [Countable K] in
/-- Both KEM message branches share the same measure decomposition into real and random keys. -/
lemma evalDist_kemGame (hkey : 𝒟[key] Set.univ = 1) (side : Bool) :
    𝒟[kemGame prepare encaps finish coin key side] =
      𝒟[coin >>= fun b => (if b then hybrid prepare encaps finish key true side
        else hybrid prepare encaps finish key false side) >>= fun z => pure (b == z)] := by
  unfold kemGame
  rw [evalDist_bind_bind_swap prepare coin _
    (measurable_from_prod_countable_left fun _ => .of_discrete)]
  rw [evalDist_bind_of_discrete coin, evalDist_bind_of_discrete coin]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro b
  cases b
  · simp only [Bool.false_eq_true, ite_false, hybrid, bind_assoc]
  · simp only [ite_true, hybrid, bind_assoc, pure_bind]
    simp only [evalDist_bind_of_discrete]
    apply Measure.bind_congr_right (Filter.Eventually.of_forall fun a => ?_)
    apply Measure.bind_congr_right (Filter.Eventually.of_forall fun ck => ?_)
    rw [Measure.bind_const, hkey, one_smul]

/-- Independent-key interchange identifies the DEM experiment with the two random-key branches. -/
lemma evalDist_demGame :
    𝒟[demGame prepare encaps finish coin key] =
      𝒟[coin >>= fun b => (if b then hybrid prepare encaps finish key false false
        else hybrid prepare encaps finish key false true) >>= fun z => pure (b == z)] := by
  unfold demGame
  rw [evalDist_bind_of_discrete coin, evalDist_bind_of_discrete coin]
  apply Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ?_)
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
    Bool.not_true, hybrid, bind_assoc]
  all_goals
    rw [evalDist_bind_bind_swap key prepare _
      (measurable_from_prod_countable_right fun _ => .of_discrete)]
    rw [evalDist_bind_of_discrete prepare, evalDist_bind_of_discrete prepare]
    apply Measure.bind_congr_right (Filter.Eventually.of_forall fun a => ?_)
    exact evalDist_bind_bind_swap key (encaps a) _
      (measurable_from_prod_countable_right fun _ => .of_discrete)

/-- The composed bias is bounded by the two KEM biases and the DEM bias. -/
lemma bias_compose_le
    (hcT : 𝒟[coin] {true} = 1 / 2) (hcF : 𝒟[coin] {false} = 1 / 2)
    (hkey : 𝒟[key] Set.univ = 1)
    (htotal : ∀ real side, 𝒟[hybrid prepare encaps finish key real side] {true} +
      𝒟[hybrid prepare encaps finish key real side] {false} = 1) :
    (𝒟[composedGame prepare encaps finish coin]).boolBias ≤
      (𝒟[kemGame prepare encaps finish coin key true]).boolBias +
      (𝒟[kemGame prepare encaps finish coin key false]).boolBias +
      (𝒟[demGame prepare encaps finish coin key]).boolBias := by
  have hbranch (p q : m Bool) (hp : 𝒟[p] {true} + 𝒟[p] {false} = 1)
      (hq : 𝒟[q] {true} + 𝒟[q] {false} = 1) :
      (𝒟[coin >>= fun b => (if b then p else q) >>= fun z => pure (b == z)]).boolBias =
        (𝒟[p]).boolDist 𝒟[q] := by
    simp only [evalDist_bind_of_discrete, evalDist_pure]
    have hif (b : Bool) : 𝒟[if b then p else q] =
        (if b then 𝒟[p] else 𝒟[q]) := by cases b <;> rfl
    simp_rw [hif]
    exact Measure.boolBias_bind_coin _ _ _ hcT hcF hp hq
  rw [composedGame_eq prepare encaps finish coin key,
    evalDist_kemGame prepare encaps finish coin key hkey true,
    evalDist_kemGame prepare encaps finish coin key hkey false,
    evalDist_demGame prepare encaps finish coin key,
    hbranch _ _ (htotal true true) (htotal true false),
    hbranch _ _ (htotal true true) (htotal false true),
    hbranch _ _ (htotal true false) (htotal false false),
    hbranch _ _ (htotal false false) (htotal false true)]
  have h₁ := Measure.boolDist_triangle
    𝒟[hybrid prepare encaps finish key true true]
    𝒟[hybrid prepare encaps finish key false true]
    𝒟[hybrid prepare encaps finish key true false]
  have h₂ := Measure.boolDist_triangle
    𝒟[hybrid prepare encaps finish key false true]
    𝒟[hybrid prepare encaps finish key false false]
    𝒟[hybrid prepare encaps finish key true false]
  rw [Measure.boolDist_comm 𝒟[hybrid prepare encaps finish key false false]
    𝒟[hybrid prepare encaps finish key true false],
    Measure.boolDist_comm 𝒟[hybrid prepare encaps finish key false true]
      𝒟[hybrid prepare encaps finish key false false]] at h₂
  linarith

end KEMDEM
