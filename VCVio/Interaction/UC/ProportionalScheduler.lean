/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.ScheduledSamplerFactorization
public import PolyFun.Interaction.UC.ScheduledOpenProcessModel
public import VCVio.EvalDist.Fintype
public import VCVio.EvalDist.Monad.Map
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Proportional UC scheduling

This module instantiates PolyFun's mass-aware binary scheduler in `ProbComp`.
A binary node draws uniformly from all slots in its two subtrees and selects
the subtree containing the drawn slot. Thus a leaf with mass `w` is selected
with probability `w` divided by the total mass, independently of how the
composition tree is parenthesized.

The coherence law is deliberately denotational: two scheduler computations
are related when every output has the same probability. The underlying oracle
programs may issue differently shaped uniform queries after reassociation, but
the induced observable distributions agree.
-/

public section

universe u

namespace Interaction
namespace UC

open OpenProcessFactorization OracleComp

namespace ProportionalScheduler

/-! ## Denotational relation -/

/-- Pointwise equality of output probabilities for `ProbComp` computations.
This is the discrete denotational equality used for scheduler coherence. -/
noncomputable def outputRel : MonadRelFamily ProbComp where
  rel := fun left right => ∀ output, Pr[= output | left] = Pr[= output | right]
  refl _ _ := rfl
  symm h output := (h output).symm
  trans h₁ h₂ output := (h₁ output).trans (h₂ output)
  map_congr := by
    intro α β f left right h output
    rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
    exact tsum_congr fun input => by rw [h input]
  bind_congr := by
    intro α β left right f h output
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    exact tsum_congr fun input => by rw [h input]

@[simp]
theorem outputRel_rel {α : Type} (left right : ProbComp α) :
    outputRel.rel left right ↔
      ∀ output, Pr[= output | left] = Pr[= output | right] :=
  Iff.rfl

/-- A finite sum over lifted Booleans has exactly its two expected terms. -/
theorem sum_ulift_bool (f : ULift Bool → ENNReal) :
    ∑ choice, f choice = f (ULift.up false) + f (ULift.up true) := by
  have univ_eq : (Finset.univ : Finset (ULift Bool)) =
      {ULift.up false, ULift.up true} := by
    ext choice
    obtain ⟨choice⟩ := choice
    cases choice <;> simp
  rw [univ_eq]
  simp

/-! ## Uniform slot draws -/

/-- A uniform draw from the positive set of slots represented by `mass`. -/
noncomputable def drawSlot (mass : ScheduleMass) : ProbComp (Fin mass.value) :=
  letI : Nonempty (Fin mass.value) := ⟨⟨0, mass.positive⟩⟩
  letI := SampleableType.ofFintype (Fin mass.value)
  $ᵗ (Fin mass.value)

/-- The number of indices below `cut` inside `Fin total` is `cut`. -/
theorem card_filter_fin_lt (cut total : Nat) (hcut : cut ≤ total) :
    ((Finset.univ : Finset (Fin total)).filter fun index => index.val < cut).card = cut := by
  let e : {index : Fin total // index.val < cut} ≃ Fin cut :=
    { toFun := fun index => ⟨index.val.val, index.property⟩
      invFun := fun index =>
        ⟨⟨index.val, lt_of_lt_of_le index.isLt hcut⟩, index.isLt⟩
      left_inv := fun index => by ext; rfl
      right_inv := fun index => by ext; rfl }
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_congr e

/-- The number of indices in the half-open interval `[lower, upper)` inside
`Fin total` is `upper - lower`. -/
theorem card_filter_fin_Ico (lower upper total : Nat)
    (hlower : lower ≤ upper) (hupper : upper ≤ total) :
    ((Finset.univ : Finset (Fin total)).filter fun index =>
      lower ≤ index.val ∧ index.val < upper).card = upper - lower := by
  let e : {index : Fin total // lower ≤ index.val ∧ index.val < upper} ≃
      Fin (upper - lower) :=
    { toFun := fun index => ⟨index.val.val - lower, by omega⟩
      invFun := fun index => by
        have hindex := index.isLt
        have hltUpper : lower + index.val < upper := by omega
        exact ⟨⟨lower + index.val, lt_of_lt_of_le hltUpper hupper⟩,
          Nat.le_add_right lower index.val, hltUpper⟩
      left_inv := fun index => by
        apply Subtype.ext
        apply Fin.ext
        simp only
        exact Nat.add_sub_of_le index.property.1
      right_inv := fun index => by
        apply Fin.ext
        simp }
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_congr e

/-- A uniform slot draw gives any decidable event its relative cardinality. -/
theorem probEvent_drawSlot (mass : ScheduleMass) (p : Fin mass.value → Prop)
    [DecidablePred p] :
    Pr[ p | drawSlot mass] =
      ((Finset.univ.filter p).card : ENNReal) / mass.value := by
  simp [drawSlot, probEvent_uniformSample, Fintype.card_fin]

/-! ## Binary and flat schedulers -/

/-- Select the left subtree exactly when the uniformly drawn slot lies in the
left subtree's initial segment. -/
noncomputable def binary : BinaryScheduler ProbComp :=
  fun left right =>
    (fun slot => ULift.up (decide (slot.val < left.value))) <$> drawSlot (left + right)

/-- Point probability of proportional binary scheduling. -/
theorem probOutput_binary (left right : ScheduleMass) (choice : ULift Bool) :
    Pr[= choice | binary left right] =
      if choice.down then
        (left.value : ENNReal) / (left.value + right.value)
      else
        (right.value : ENNReal) / (left.value + right.value) := by
  rw [binary, probOutput_map]
  obtain ⟨choice⟩ := choice
  cases choice
  · rw [probEvent_drawSlot]
    simp only [Bool.false_eq]
    have hevent :
        ((Finset.univ : Finset (Fin (left + right).value)).filter
          fun index => ULift.up (decide (index.val < left.value)) = ULift.up false) =
        (Finset.univ.filter fun index => ¬index.val < left.value) := by
      ext index
      simp
    rw [hevent]
    have hcard :
        ((Finset.univ : Finset (Fin (left + right).value)).filter
          fun index => ¬index.val < left.value).card = right.value := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (left + right).value)))
        (fun index => index.val < left.value)
      rw [Finset.card_univ, Fintype.card_fin,
        card_filter_fin_lt left.value (left + right).value (by simp)] at hpartition
      simpa using hpartition
    rw [hcard]
    simp
  · rw [probEvent_drawSlot]
    have hevent :
        ((Finset.univ : Finset (Fin (left + right).value)).filter
          fun index => ULift.up (decide (index.val < left.value)) = ULift.up true) =
        (Finset.univ.filter fun index => index.val < left.value) := by
      ext index
      simp
    rw [hevent]
    rw [card_filter_fin_lt left.value (left + right).value (by simp)]
    simp

/-- Classify a slot in a three-way frontier. -/
def classifyThree (first second : ScheduleMass) {total : Nat}
    (slot : Fin total) : ULift Leaf :=
  if slot.val < first.value then
    ULift.up .first
  else if slot.val < first.value + second.value then
    ULift.up .second
  else
    ULift.up .context

/-- Direct parenthesization-free draw from three component frontiers. -/
noncomputable def flat : BinaryScheduler.FlatChoice ProbComp :=
  fun first second context =>
    classifyThree first second <$> drawSlot (first + second + context)

/-- Point probability of the direct three-way scheduler. -/
theorem probOutput_flat (first second context : ScheduleMass) (leaf : ULift Leaf) :
    Pr[= leaf | flat first second context] =
      match leaf.down with
      | .first => (first.value : ENNReal) /
          (first.value + second.value + context.value)
      | .second => (second.value : ENNReal) /
          (first.value + second.value + context.value)
      | .context => (context.value : ENNReal) /
          (first.value + second.value + context.value) := by
  rw [flat, probOutput_map]
  obtain ⟨leaf⟩ := leaf
  cases leaf
  all_goals rw [probEvent_drawSlot]
  · have hevent :
        ((Finset.univ : Finset (Fin (first + second + context).value)).filter
          fun slot => classifyThree first second slot = ULift.up Leaf.first) =
        (Finset.univ.filter fun slot => slot.val < first.value) := by
      ext slot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold classifyThree
      split_ifs <;> simp_all
    rw [hevent, card_filter_fin_lt first.value (first + second + context).value
      (by simp only [ScheduleMass.value_add]; omega)]
    simp
  · have hevent :
        ((Finset.univ : Finset (Fin (first + second + context).value)).filter
          fun slot => classifyThree first second slot = ULift.up Leaf.second) =
        (Finset.univ.filter fun slot =>
          first.value ≤ slot.val ∧ slot.val < first.value + second.value) := by
      ext slot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold classifyThree
      split_ifs <;> simp_all
    rw [hevent, card_filter_fin_Ico first.value (first.value + second.value)
      (first + second + context).value (by omega)
        (by simp only [ScheduleMass.value_add]; omega)]
    simp
  · have hevent :
        ((Finset.univ : Finset (Fin (first + second + context).value)).filter
          fun slot => classifyThree first second slot = ULift.up Leaf.context) =
        (Finset.univ.filter fun slot =>
          ¬slot.val < first.value + second.value) := by
      ext slot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold classifyThree
      split_ifs <;> simp_all
      omega
    rw [hevent]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (first + second + context).value)))
      (fun slot => slot.val < first.value + second.value)
    rw [Finset.card_univ, Fintype.card_fin,
      card_filter_fin_lt (first.value + second.value)
        (first + second + context).value
        (by simp only [ScheduleMass.value_add]; omega)] at hpartition
    simp only [ScheduleMass.value_add] at hpartition
    have hcard :
        ((Finset.univ : Finset (Fin (first + second + context).value)).filter
          fun slot => ¬slot.val < first.value + second.value).card = context.value := by
      exact Nat.add_left_cancel hpartition
    rw [hcard]
    simp

/-- Multiplying a component's conditional share by its combined frontier's
outer share cancels the intermediate mass. -/
theorem nested_ratio (selected combined context : Nat) (hcombined : 0 < combined) :
    (combined : ENNReal) / (combined + context) *
        ((selected : ENNReal) / combined) =
      (selected : ENNReal) / (combined + context) := by
  have hzero : (combined : ENNReal) ≠ 0 := by
    simp [Nat.ne_of_gt hcombined]
  have htop : (combined : ENNReal) ≠ ⊤ := by simp
  rw [mul_comm, ← mul_div_assoc, ENNReal.div_mul_cancel hzero htop]

/-! ## Coherence -/

/-- Proportional scheduling factors every hierarchical three-way draw through
the same direct distribution. -/
theorem isFlat : BinaryScheduler.IsFlat outputRel binary flat := by
  constructor
  · intro left right
    rw [outputRel_rel]
    intro choice
    rw [probOutput_binary, probOutput_map]
    obtain ⟨choice⟩ := choice
    cases choice
    all_goals simp [BinaryScheduler.flip, probOutput_binary,
      probEvent_eq_tsum_indicator, sum_ulift_bool, add_comm]
  · intro first second context
    rw [outputRel_rel]
    intro leaf
    obtain ⟨leaf⟩ := leaf
    cases leaf
    all_goals simp [BinaryScheduler.sourceDraw, probOutput_bind_eq_sum_fintype,
      sum_ulift_bool, probOutput_binary, probOutput_flat, probOutput_pure]
    · simpa only [Nat.cast_add] using
        nested_ratio first.value (first.value + second.value) context.value
          (Nat.add_pos_left first.positive _)
    · simpa only [Nat.cast_add] using
        nested_ratio second.value (first.value + second.value) context.value
          (Nat.add_pos_left first.positive _)
  · intro first second context
    rw [outputRel_rel]
    intro leaf
    obtain ⟨leaf⟩ := leaf
    cases leaf
    all_goals simp [BinaryScheduler.leftDraw, probOutput_bind_eq_sum_fintype,
      sum_ulift_bool, probOutput_binary, probOutput_flat, probOutput_pure,
      add_comm, add_assoc]
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio second.value (context.value + second.value) first.value
          (Nat.add_pos_left context.positive _)
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio context.value (context.value + second.value) first.value
          (Nat.add_pos_left context.positive _)
  · intro first second context
    rw [outputRel_rel]
    intro leaf
    obtain ⟨leaf⟩ := leaf
    cases leaf
    all_goals simp [BinaryScheduler.rightDraw, probOutput_bind_eq_sum_fintype,
      sum_ulift_bool, probOutput_binary, probOutput_flat, probOutput_pure,
      add_comm, add_left_comm, add_assoc]
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio first.value (context.value + first.value) second.value
          (Nat.add_pos_left context.positive _)
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio context.value (context.value + first.value) second.value
          (Nat.add_pos_left context.positive _)

/-- Proportional scheduling satisfies the swap and reassociation laws consumed
by PolyFun's scheduled sampler-factorization bridge. -/
theorem isCoherent : BinaryScheduler.IsCoherent outputRel binary :=
  isFlat.isCoherent

/-- The mass-aware open-process theory instantiated with proportional
`ProbComp` scheduling. -/
noncomputable abbrev theory (Party : Type u) : OpenTheory :=
  scheduledOpenTheory Party ProbComp binary

end ProportionalScheduler

end UC
end Interaction
