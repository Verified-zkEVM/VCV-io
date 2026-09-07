/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.AdaptivePrefix

/-!
# Safe Shared-Log Potential for Merkle Multi-Extractability

This module owns the arithmetic security budget for a finite family of Merkle commitment
checkpoints sharing one random-oracle log. If the extracted checkpoint trees contain at most
`nodeBudget` nodes in total and there are `checkpointCount` roots, then a log backed by `k`
distinct oracle keys exposes at most

`min nodeBudget (2 * k + checkpointCount)`

distinct candidate labels: every populated key contributes its two ordered children and every
checkpoint contributes its root. This shared-log cap is strictly sharper than multiplying the
single-tree `min (2L - 1) (2k + 1)` cap by the number of checkpoints.

The error numerator is a finite maximum over fresh adversarial inputs across every commitment
phase and terminal opening production. It deliberately overcharges queries made before a target
exists. `MultiExtractability.OnlineBound` proves the checkpoint-aware stopping recurrence for this
envelope; this module still does not identify it with a tighter textbook potential. Coarse closed
forms are derived below as corollaries.
-/

@[expose] public section

namespace MerkleTreeMultiExtractability

open OracleComp

/-- Sharp structural cap on the union of labels reachable in all checkpoint extractions from a
shared log containing `keyCount` populated complete queries. -/
def sharedExtractedLabelCountBound (nodeBudget checkpointCount keyCount : ℕ) : ℕ :=
  min nodeBudget (2 * keyCount + checkpointCount)

/-- Multi-checkpoint error numerator after `prefixMisses` fresh inputs. In addition to cache
collision terms, the shared target set is charged against the entire remaining adversarial budget:
a later commitment query may hit a target of an earlier checkpoint even before the terminal
opening suffix begins. -/
def multiCheckpointErrorNumeratorAtMissCount
    (nodeBudget checkpointCount verifierOverhead remaining cached prefixMisses : ℕ) : ℕ :=
  prefixMisses * cached + prefixMisses.choose 2 +
    sharedExtractedLabelCountBound nodeBudget checkpointCount (cached + prefixMisses) *
      (remaining + verifierOverhead)

/-- Finite maximum of the multi-checkpoint error numerator over every feasible number of fresh
prefix inputs. -/
def multiCheckpointErrorNumerator
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) : ℕ :=
  (Finset.range (remaining + 1)).sup fun prefixMisses =>
    multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
      remaining cached prefixMisses

/-- Unrelaxed shared-ROM error numerator from an empty cache. -/
def multiCheckpointROMErrorNumerator
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) : ℕ :=
  multiCheckpointErrorNumerator
    nodeBudget checkpointCount verifierOverhead queryBound 0

/-- The safe, unrelaxed numerator is the finite maximum over every feasible number of fresh
adversarial inputs.
This theorem is the intended rewrite interface for audits and downstream arithmetic relaxations. -/
theorem multiCheckpointROMErrorNumerator_eq_sup
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiCheckpointROMErrorNumerator
        nodeBudget checkpointCount verifierOverhead queryBound =
      (Finset.range (queryBound + 1)).sup fun prefixMisses =>
        prefixMisses.choose 2 +
          min nodeBudget (2 * prefixMisses + checkpointCount) *
            (queryBound + verifierOverhead) := by
  simp [multiCheckpointROMErrorNumerator, multiCheckpointErrorNumerator,
    multiCheckpointErrorNumeratorAtMissCount, sharedExtractedLabelCountBound]

/-- Shared extraction never exposes more candidates than the total node budget. -/
theorem sharedExtractedLabelCountBound_le_nodeBudget
    (nodeBudget checkpointCount keyCount : ℕ) :
    sharedExtractedLabelCountBound nodeBudget checkpointCount keyCount ≤ nodeBudget :=
  Nat.min_le_left _ _

/-- Shared extraction never exposes more than two children per populated complete query plus one
root per checkpoint. -/
theorem sharedExtractedLabelCountBound_le_querySupport
    (nodeBudget checkpointCount keyCount : ℕ) :
    sharedExtractedLabelCountBound nodeBudget checkpointCount keyCount ≤
      2 * keyCount + checkpointCount :=
  Nat.min_le_right _ _

/-- The safe shared-target cap is monotone as fresh complete-query keys accumulate. -/
theorem sharedExtractedLabelCountBound_mono_keyCount
    (nodeBudget checkpointCount : ℕ) :
    Monotone (sharedExtractedLabelCountBound nodeBudget checkpointCount) := by
  intro left right hle
  unfold sharedExtractedLabelCountBound
  gcongr

/-- The shared target cap is monotone in both global resource envelopes. -/
theorem sharedExtractedLabelCountBound_mono_budget
    {leftNodeBudget rightNodeBudget leftCheckpointCount rightCheckpointCount keyCount : ℕ}
    (hnodes : leftNodeBudget ≤ rightNodeBudget)
    (hcheckpoints : leftCheckpointCount ≤ rightCheckpointCount) :
    sharedExtractedLabelCountBound leftNodeBudget leftCheckpointCount keyCount ≤
      sharedExtractedLabelCountBound rightNodeBudget rightCheckpointCount keyCount := by
  unfold sharedExtractedLabelCountBound
  gcongr

/-- Enlarging the global node/checkpoint envelope can only enlarge the online energy. -/
theorem multiCheckpointErrorNumeratorAtMissCount_mono_budget
    {leftNodeBudget rightNodeBudget leftCheckpointCount rightCheckpointCount : ℕ}
    (hnodes : leftNodeBudget ≤ rightNodeBudget)
    (hcheckpoints : leftCheckpointCount ≤ rightCheckpointCount)
    (verifierOverhead remaining cached prefixMisses : ℕ) :
    multiCheckpointErrorNumeratorAtMissCount leftNodeBudget leftCheckpointCount verifierOverhead
        remaining cached prefixMisses ≤
      multiCheckpointErrorNumeratorAtMissCount rightNodeBudget rightCheckpointCount verifierOverhead
        remaining cached prefixMisses := by
  unfold multiCheckpointErrorNumeratorAtMissCount
  gcongr
  exact sharedExtractedLabelCountBound_mono_budget hnodes hcheckpoints

/-- Enlarging the global node/checkpoint envelope can only enlarge the safe potential. -/
theorem multiCheckpointErrorNumerator_mono_budget
    {leftNodeBudget rightNodeBudget leftCheckpointCount rightCheckpointCount : ℕ}
    (hnodes : leftNodeBudget ≤ rightNodeBudget)
    (hcheckpoints : leftCheckpointCount ≤ rightCheckpointCount)
    (verifierOverhead remaining cached : ℕ) :
    multiCheckpointErrorNumerator leftNodeBudget leftCheckpointCount verifierOverhead
        remaining cached ≤
      multiCheckpointErrorNumerator rightNodeBudget rightCheckpointCount verifierOverhead
        remaining cached := by
  unfold multiCheckpointErrorNumerator
  apply Finset.sup_mono_fun
  intro prefixMisses _
  exact multiCheckpointErrorNumeratorAtMissCount_mono_budget hnodes hcheckpoints
    verifierOverhead remaining cached prefixMisses

/-- More remaining adversarial syntax can only enlarge the online energy. -/
theorem multiCheckpointErrorNumeratorAtMissCount_mono_remaining
    (nodeBudget checkpointCount verifierOverhead cached prefixMisses : ℕ) :
    Monotone fun remaining =>
      multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
        remaining cached prefixMisses := by
  intro left right hremaining
  unfold multiCheckpointErrorNumeratorAtMissCount
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hremaining verifierOverhead)

/-- The safe potential is monotone in the remaining adversarial query budget. -/
theorem multiCheckpointErrorNumerator_mono_remaining
    (nodeBudget checkpointCount verifierOverhead cached : ℕ) :
    Monotone fun remaining =>
      multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        remaining cached := by
  intro left right hremaining
  unfold multiCheckpointErrorNumerator
  apply Finset.sup_le
  intro prefixMisses hprefix
  apply (multiCheckpointErrorNumeratorAtMissCount_mono_remaining nodeBudget checkpointCount
    verifierOverhead cached prefixMisses hremaining).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hprefix ⊢
  omega

/-- Fresh-miss recurrence behind the safe online envelope. The local step pays collision against
the existing cache and a hit in the target set predictable before sampling; the continuation then
uses the enlarged cache. -/
theorem multiCheckpointErrorNumeratorAtMissCount_miss_step
    (nodeBudget checkpointCount verifierOverhead remaining cached continuationMisses : ℕ)
    (hremaining : 0 < remaining) :
    cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached +
        multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
          (remaining - 1) (cached + 1) continuationMisses ≤
      multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
        remaining cached (continuationMisses + 1) := by
  have hkeys : cached + 1 + continuationMisses =
      cached + (continuationMisses + 1) := by omega
  have hchoose : (continuationMisses + 1).choose 2 =
      continuationMisses + continuationMisses.choose 2 := by
    rw [show continuationMisses + 1 = continuationMisses.succ by omega,
      Nat.choose_succ_succ]
    simp
  have htarget := sharedExtractedLabelCountBound_mono_keyCount nodeBudget checkpointCount
    (show cached ≤ cached + (continuationMisses + 1) by omega)
  have htargetTerm :
      sharedExtractedLabelCountBound nodeBudget checkpointCount cached +
          sharedExtractedLabelCountBound nodeBudget checkpointCount
              (cached + (continuationMisses + 1)) *
            (remaining - 1 + verifierOverhead) ≤
        sharedExtractedLabelCountBound nodeBudget checkpointCount
            (cached + (continuationMisses + 1)) *
          (remaining + verifierOverhead) := by
    calc
      _ ≤ sharedExtractedLabelCountBound nodeBudget checkpointCount
              (cached + (continuationMisses + 1)) +
            sharedExtractedLabelCountBound nodeBudget checkpointCount
                (cached + (continuationMisses + 1)) *
              (remaining - 1 + verifierOverhead) :=
        Nat.add_le_add_right htarget _
      _ = _ := by
        have hremaining' : remaining + verifierOverhead =
            (remaining - 1 + verifierOverhead) + 1 := by omega
        rw [hremaining', Nat.mul_succ]
        omega
  have hcollision :
      cached + continuationMisses * (cached + 1) + continuationMisses.choose 2 =
        (continuationMisses + 1) * cached + (continuationMisses + 1).choose 2 := by
    rw [hchoose]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  unfold multiCheckpointErrorNumeratorAtMissCount
  rw [hkeys]
  calc
    cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached +
          (continuationMisses * (cached + 1) + continuationMisses.choose 2 +
            sharedExtractedLabelCountBound nodeBudget checkpointCount
                (cached + (continuationMisses + 1)) *
              (remaining - 1 + verifierOverhead)) =
        (cached + continuationMisses * (cached + 1) + continuationMisses.choose 2) +
          (sharedExtractedLabelCountBound nodeBudget checkpointCount cached +
            sharedExtractedLabelCountBound nodeBudget checkpointCount
                (cached + (continuationMisses + 1)) *
              (remaining - 1 + verifierOverhead)) := by ac_rfl
    _ ≤ ((continuationMisses + 1) * cached + (continuationMisses + 1).choose 2) +
          sharedExtractedLabelCountBound nodeBudget checkpointCount
              (cached + (continuationMisses + 1)) *
            (remaining + verifierOverhead) :=
      Nat.add_le_add (le_of_eq hcollision) htargetTerm
    _ = _ := rfl

private theorem multiCheckpointErrorNumeratorAtMissCount_zero
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) :
    multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
        remaining cached 0 =
      sharedExtractedLabelCountBound nodeBudget checkpointCount cached *
        (remaining + verifierOverhead) := by
  simp [multiCheckpointErrorNumeratorAtMissCount]

/-- Terminal target-hit budget is contained in the safe finite maximum. -/
theorem multiCheckpointErrorNumerator_terminal_le
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) :
    sharedExtractedLabelCountBound nodeBudget checkpointCount cached *
        (remaining + verifierOverhead) ≤
      multiCheckpointErrorNumerator
        nodeBudget checkpointCount verifierOverhead remaining cached := by
  rw [← multiCheckpointErrorNumeratorAtMissCount_zero]
  exact Finset.le_sup (by simp)

private theorem multiCheckpointErrorNumeratorAtMissCount_hit_le
    (nodeBudget checkpointCount verifierOverhead remaining cached misses : ℕ) :
    multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
        (remaining - 1) cached misses ≤
      multiCheckpointErrorNumeratorAtMissCount nodeBudget checkpointCount verifierOverhead
        remaining cached misses := by
  unfold multiCheckpointErrorNumeratorAtMissCount
  gcongr
  omega

/-- A cached query consumes remaining budget without increasing the cache or target cap. -/
theorem multiCheckpointErrorNumerator_hit_le
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ) :
    multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        (remaining - 1) cached ≤
      multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        remaining cached := by
  unfold multiCheckpointErrorNumerator
  apply Finset.sup_le
  intro misses hmisses
  apply (multiCheckpointErrorNumeratorAtMissCount_hit_le nodeBudget checkpointCount verifierOverhead
    remaining cached misses).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hmisses ⊢
  omega

/-- One fresh miss pays collision plus predictable live-target hit, then recurs with one more
populated key and one fewer query. -/
theorem multiCheckpointErrorNumerator_miss_le
    (nodeBudget checkpointCount verifierOverhead remaining cached : ℕ)
    (hremaining : 0 < remaining) :
    cached + sharedExtractedLabelCountBound nodeBudget checkpointCount cached +
        multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
          (remaining - 1) (cached + 1) ≤
      multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        remaining cached := by
  unfold multiCheckpointErrorNumerator
  rw [Finset.add_sup (by simp)]
  apply Finset.sup_le
  intro continuationMisses hmisses
  apply (multiCheckpointErrorNumeratorAtMissCount_miss_step nodeBudget checkpointCount
    verifierOverhead remaining cached continuationMisses hremaining).trans
  apply Finset.le_sup
  simp only [Finset.mem_range] at hmisses ⊢
  omega

/-- Coarse closed form obtained from the safe finite maximum by separately maximizing the
birthday and target-hit terms. -/
theorem multiCheckpointROMErrorNumerator_le_coarse
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiCheckpointROMErrorNumerator
        nodeBudget checkpointCount verifierOverhead queryBound ≤
      queryBound.choose 2 + nodeBudget * (queryBound + verifierOverhead) := by
  rw [multiCheckpointROMErrorNumerator_eq_sup]
  apply Finset.sup_le
  intro prefixMisses hprefix
  simp only [Finset.mem_range] at hprefix
  have hmisses : prefixMisses ≤ queryBound := by omega
  have hchoose : prefixMisses.choose 2 ≤ queryBound.choose 2 :=
    Nat.choose_le_choose 2 hmisses
  have htarget : min nodeBudget (2 * prefixMisses + checkpointCount) ≤ nodeBudget :=
    Nat.min_le_left _ _
  exact Nat.add_le_add hchoose (Nat.mul_le_mul_right _ htarget)

/-- A still simpler quadratic relaxation, useful when a consumer does not want binomial
coefficients in its public statement. -/
theorem multiCheckpointROMErrorNumerator_le_quadratic
    (nodeBudget checkpointCount verifierOverhead queryBound : ℕ) :
    multiCheckpointROMErrorNumerator
        nodeBudget checkpointCount verifierOverhead queryBound ≤
      queryBound * queryBound + nodeBudget * (queryBound + verifierOverhead) := by
  exact (multiCheckpointROMErrorNumerator_le_coarse
    nodeBudget checkpointCount verifierOverhead queryBound).trans (by
      gcongr
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans
        (Nat.mul_le_mul_left queryBound (Nat.sub_le queryBound 1)))

end MerkleTreeMultiExtractability
