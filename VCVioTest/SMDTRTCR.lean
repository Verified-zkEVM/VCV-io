/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTRTCR

/-!
# SM-DT-rTCR canaries

These concrete games pin the parts of the definition that no build gate can see: that a win is
claimed on the `(message, randomness)` pair rather than on the message, that an exhausted slot loses
but still consumes a target, and that the history is in issue order.

The probe hash discards its randomness part, so every pair sharing a message collides. That is what
makes the same-message win observable at all.
-/

public section

open OracleComp OracleSpec TweakableHash

namespace SMDTRTCRTest

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

/-- The digest is the message part alone, so `(m, ρ)` and `(m, ρ')` always collide. -/
@[expose] def hash : TweakableHash Seed Bool (Bool × Bool) Bool where
  seedGen := $ᵗ Seed
  eval _ _ m := m.1

/-- Room for two targets, a three-attempt budget, and a predicate that always accepts, so the
resampling loop stops on its first draw and leaves the remaining budget unspent. -/
@[expose] def acceptingProblem : SM_DT_RTCR_Problem Seed Bool Bool Bool Bool where
  th := hash
  prop := fun _ => true
  numTargets := 2
  numRetries := 3

/-- One target and a predicate that never accepts, so every query exhausts its budget. -/
@[expose] def exhaustingProblem : SM_DT_RTCR_Problem Seed Bool Bool Bool Bool where
  th := hash
  prop := fun _ => false
  numTargets := 1
  numRetries := 3

@[simp] lemma acceptingProblem_seedGen : acceptingProblem.th.seedGen = pure .only := rfl

@[simp] lemma exhaustingProblem_seedGen : exhaustingProblem.th.seedGen = pure .only := rfl

abbrev Specs := unifSpec + SM_DT_RTCR_challengeSpec Bool Bool Bool Bool

def challenge (t m : Bool) : OracleComp Specs (Option (Bool × Bool)) :=
  liftM (Specs.query (.inr (t, m)))

/-- Claims the recorded message back with the *other* randomness. The digests agree because the hash
discards the randomness, and the pairs differ, so this wins whichever randomness was drawn. -/
def sameMessageFreshRandomness : SM_DT_RTCR_Adversary acceptingProblem where
  main _ := do
    let answer ← challenge false true
    return (0, true, !(answer.map Prod.snd).getD false)

/-- Claims the recorded pair back unchanged, which must lose. -/
def replayRecordedPair : SM_DT_RTCR_Adversary acceptingProblem where
  main _ := do
    let answer ← challenge false true
    return (0, true, (answer.map Prod.snd).getD false)

/-- Claims an index past the end of a one-entry history. -/
def indexOutOfRange : SM_DT_RTCR_Adversary acceptingProblem where
  main _ := do
    let _ ← challenge false true
    return (5, true, true)

/-- Claims the slot recorded when resampling was exhausted. -/
def claimExhaustedSlot : SM_DT_RTCR_Adversary exhaustingProblem where
  main _ := do
    let _ ← challenge false true
    return (0, true, true)

/-- Two accepted queries at distinct tweaks. -/
def twoQueries : OracleComp Specs Unit := do
  let _ ← challenge false true
  let _ ← challenge true false
  return ()

/-- An exhausting query, then a second query at a fresh tweak. -/
def exhaustedThenSecond : OracleComp Specs (Option (Bool × Bool)) := do
  let _ ← challenge false true
  challenge true true

/-- Reusing the recorded message with fresh randomness is a win. Transcribing SM-TCR's winning
condition, which requires the message to differ, would make this adversary lose. -/
theorem same_message_fresh_randomness_wins :
    SM_DT_RTCR_Advantage sameMessageFreshRandomness = 1 := by
  simp [SM_DT_RTCR_Advantage, SM_DT_RTCR_Experiment, SM_DT_RTCR_oracles,
    SM_DT_RTCR_challengeOracle, SM_DT_RTCR_resample, SM_DT_RTCR_IsCollision,
    sameMessageFreshRandomness, challenge, acceptingProblem, hash, TweakReserved]

/-- Replaying the recorded pair loses, so the pair inequality in the winning condition is live. -/
theorem replay_loses : SM_DT_RTCR_Advantage replayRecordedPair = 0 := by
  simp [SM_DT_RTCR_Advantage, SM_DT_RTCR_Experiment, SM_DT_RTCR_oracles,
    SM_DT_RTCR_challengeOracle, SM_DT_RTCR_resample, SM_DT_RTCR_IsCollision, replayRecordedPair,
    challenge, acceptingProblem, hash, TweakReserved]

/-- An index past the end of the history loses. -/
theorem index_out_of_range_loses : SM_DT_RTCR_Advantage indexOutOfRange = 0 := by
  simp [SM_DT_RTCR_Advantage, SM_DT_RTCR_Experiment, SM_DT_RTCR_oracles,
    SM_DT_RTCR_challengeOracle, SM_DT_RTCR_resample, SM_DT_RTCR_IsCollision, indexOutOfRange,
    challenge, acceptingProblem, hash, TweakReserved]

/-- A slot recorded on exhausted resampling cannot be forged against, even though the probe hash
collides on everything. -/
theorem exhausted_slot_loses : SM_DT_RTCR_Advantage claimExhaustedSlot = 0 := by
  simp [SM_DT_RTCR_Advantage, SM_DT_RTCR_Experiment, SM_DT_RTCR_oracles,
    SM_DT_RTCR_challengeOracle, SM_DT_RTCR_resample, SM_DT_RTCR_IsCollision, claimExhaustedSlot,
    challenge, exhaustingProblem, hash, TweakReserved]

/-- An exhausted query consumes one of the `numTargets` targets: at a cap of one, the query that
returned nothing still fills the history, and the next query at a fresh tweak is refused. This is
the formalization decision the paper leaves open, so it is pinned end to end rather than only at the
oracle. -/
theorem exhausted_burns_a_target :
    ∀ z ∈ support ((simulateQ (SM_DT_RTCR_oracles exhaustingProblem .only)
      exhaustedThenSecond).run []),
      z = (none, [(false, true, none)]) := by
  simp [exhaustedThenSecond, challenge, SM_DT_RTCR_oracles, SM_DT_RTCR_challengeOracle,
    SM_DT_RTCR_resample, exhaustingProblem, hash, TweakReserved]

/-- Whatever randomness the oracle draws, the tweaks appear in issue order, so the `j`-th entry
belongs to the `j`-th query. Appending is what makes this hold; consing would reverse it. -/
theorem history_in_issue_order :
    ∀ z ∈ support ((simulateQ (SM_DT_RTCR_oracles acceptingProblem .only) twoQueries).run []),
      z.2.map Prod.fst = [false, true] := by
  simp [twoQueries, challenge, SM_DT_RTCR_oracles, SM_DT_RTCR_challengeOracle,
    SM_DT_RTCR_resample, acceptingProblem, hash, TweakReserved]
  grind

end SMDTRTCRTest
