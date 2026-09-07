/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# End-to-end canaries for SM-DT-TCR and the collection oracle

The pins in `HardnessAssumptions/TweakableHash/` stop at an oracle's `run`; these run the whole
game, winning condition included, on a collapsing tweakable hash where every pair of messages
collides. What is being measured is therefore the bookkeeping, not the hash: which queries the
oracles accept, in what order the challenge history records them, and which index the winning
condition then reads.

`oracle_separation_canary` checks both directions of the security-critical tweak-separation rule. A
collection query at an existing challenge tweak must return `none`; the adversary branches on that
rejection, so forgetting the check turns its toy collision into a loss. In the other order, a
challenge query at a tweak already spent on the collection oracle is rejected and leaves no target
to forge against.

The remaining canaries are chosen so that each one is the sole canary whose verdict changes under
one specific weakening of the oracles: prepending rather than appending an accepted target, dropping
the target cap, dropping the challenge-history tweak check, and reading an index the challenge
history does not have. A canary that merely restates an oracle pin would not separate those.

`win_coin` pins that the target-selection phase can sample. A reduction that simulates a signer
needs coins before the seed is revealed, so `SM_DT_TCR_Adversary.choose` runs against a `unifSpec`
summand; this canary stops elaborating if that summand goes away.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace SMDTTCRTest

/-! ## A collapsing tweakable hash

A one-element seed type keeps `seedGen` deterministic, and a constant `eval` makes every message a
collision, so a canary that loses can only be losing on the tweak discipline or the index lookup. -/

inductive Seed
  | only

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ _ := false

def problem : SM_DT_TCR_Problem Unit Seed Bool Bool Bool where
  th := hash
  thColl := collection
  numTargets := 1

/-- The same problem at a cap of two, for the canaries that need a second accepted target. -/
def problemTwo : SM_DT_TCR_Problem Unit Seed Bool Bool Bool :=
  { problem with numTargets := 2 }

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

@[simp] lemma problem_eval (pk : Seed) (tweak message : Bool) :
    problem.th.eval pk tweak message = false := rfl

@[simp] lemma problemTwo_th : problemTwo.th = problem.th := rfl

/-! ## Queries

The two caps share one collection, so a single spec abbreviation serves adversaries against either
problem. -/

abbrev Specs := unifSpec + (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec problem.thColl)

/-- Query the challenge oracle on `(tweak, message)`. -/
def challenge (tweak message : Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl (tweak, message))))

/-- Query the collection oracle on its sole member at `(tweak, message)`. -/
def collectionQuery (tweak : Bool) (message : problem.thColl.Msg ()) :
    OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), tweak, message⟩)))

/-- Draw a private coin, without the public seed. -/
def coin : OracleComp Specs (Fin 2) := liftM (Specs.query (.inl 1))

/-! ## Adversaries -/

/-- Place one target, then collide with it. -/
def challengeOnly : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge false false
    return ()
  forge _ _ := pure (0, true)

/-- Challenge first, then touch the same tweak through the collection oracle, carrying that
oracle's answer into the second phase. Forging `true` collides and `false` does not, so the game's
verdict reports whether the collection query was rejected. -/
def challengeThenCollection : SM_DT_TCR_Adversary problem where
  State := Option Bool
  choose := do
    let _ ← challenge false false
    collectionQuery false false
  forge answer _ := match answer with
    | none => pure (0, true)
    | some _ => pure (0, false)

/-- Spend the tweak on the collection oracle before challenging at it. -/
def collectionThenChallenge : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← collectionQuery false false
    let _ ← challenge false false
    return ()
  forge _ _ := pure (0, true)

/-- Two challenge queries at distinct tweaks against a cap of one, forging at the second. -/
def overCap : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge true false
    let _ ← challenge false false
    return ()
  forge _ _ := pure (1, true)

/-- Two challenge queries at the *same* tweak with different messages, below the cap, forging
against the second. -/
def reusedTweak : SM_DT_TCR_Adversary problemTwo where
  State := Unit
  choose := do
    let _ ← challenge true false
    let _ ← challenge true true
    return ()
  forge _ _ := pure (1, false)

/-- Two targets whose messages differ, forging the second one's own message at index `1`. Colliding
with a message requires differing from it, so this loses exactly when index `1` holds the *second*
target. -/
def order : SM_DT_TCR_Adversary problemTwo where
  State := Unit
  choose := do
    let _ ← challenge true false
    let _ ← challenge false true
    return ()
  forge _ _ := pure (1, true)

/-- Place one target and forge against an index the challenge history does not have. -/
def outOfRange : SM_DT_TCR_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge true false
    return ()
  forge _ _ := pure (5, true)

/-- Flip a coin during target selection, carry it into the second phase, and collide. -/
def coinFlip : SM_DT_TCR_Adversary problem where
  State := Fin 2
  choose := do
    let b ← coin
    let _ ← challenge true false
    return b
  forge _ _ := pure (0, true)

/-! ## Transcripts

One equation per adversary, fixing both the answers it receives and the histories it leaves. -/

private lemma run_challengeOnly :
    (simulateQ (SM_DT_TCR_oracles problem .only) challengeOnly.choose).run ([], []) =
      pure ((), ([(false, false)], [])) := by
  rfl

private lemma run_challengeThenCollection :
    (simulateQ (SM_DT_TCR_oracles problem .only) challengeThenCollection.choose).run ([], []) =
      pure (none, ([(false, false)], [])) := by
  rfl

private lemma run_collectionThenChallenge :
    (simulateQ (SM_DT_TCR_oracles problem .only) collectionThenChallenge.choose).run ([], []) =
      pure ((), ([], [false])) := by
  rfl

private lemma run_overCap :
    (simulateQ (SM_DT_TCR_oracles problem .only) overCap.choose).run ([], []) =
      pure ((), ([(true, false)], [])) := by
  rfl

private lemma run_reusedTweak :
    (simulateQ (SM_DT_TCR_oracles problemTwo .only) reusedTweak.choose).run ([], []) =
      pure ((), ([(true, false)], [])) := by
  rfl

private lemma run_order :
    (simulateQ (SM_DT_TCR_oracles problemTwo .only) order.choose).run ([], []) =
      pure ((), ([(true, false), (false, true)], [])) := by
  rfl

private lemma run_outOfRange :
    (simulateQ (SM_DT_TCR_oracles problem .only) outOfRange.choose).run ([], []) =
      pure ((), ([(true, false)], [])) := by
  rfl

private lemma run_coinFlip :
    (simulateQ (SM_DT_TCR_oracles problem .only) coinFlip.choose).run ([], []) =
      (do let b ← (liftM (unifSpec.query 1) : ProbComp (Fin 2));
          pure (b, ([(true, false)], []))) := by
  rfl

/-! ## Verdicts -/

/-- Both query orders enforce challenge/collection tweak separation. -/
theorem oracle_separation_canary :
    SM_DT_TCR_Experiment challengeOnly = pure true ∧
      SM_DT_TCR_Experiment challengeThenCollection = pure true ∧
      SM_DT_TCR_Experiment collectionThenChallenge = pure false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_challengeOnly]
    simp [challengeOnly, problem_eval]
  · simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_challengeThenCollection]
    simp [challengeThenCollection, problem_eval]
  · simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
    rw [run_collectionThenChallenge]
    rfl

/-- A challenge query past the target cap is rejected, so the second target never exists. -/
theorem lose_overCap : SM_DT_TCR_Experiment overCap = pure false := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_overCap]
  simp [overCap, problem_eval]

/-- A second challenge query at a tweak already in the challenge history is rejected even below the
cap, so no second target exists to forge against. -/
theorem lose_reusedTweak : SM_DT_TCR_Experiment reusedTweak = pure false := by
  simp only [SM_DT_TCR_Experiment, problemTwo_th, problem_seedGen, pure_bind]
  rw [run_reusedTweak]
  simp [reusedTweak, problem_eval]

/-- Accepted targets are appended, so index `1` holds the second one and forging its own message
fails to differ from it. -/
theorem lose_order : SM_DT_TCR_Experiment order = pure false := by
  simp only [SM_DT_TCR_Experiment, problemTwo_th, problem_seedGen, pure_bind]
  rw [run_order]
  simp [order, problem_eval]

/-- An index outside the challenge history loses. -/
theorem lose_outOfRange : SM_DT_TCR_Experiment outOfRange = pure false := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_outOfRange]
  simp [outOfRange, problem_eval]

/-- The coin drawn during target selection is threaded through to the result, and the collision
wins on either draw. -/
theorem win_coin :
    SM_DT_TCR_Experiment coinFlip =
      (liftM (unifSpec.query 1) : ProbComp (Fin 2)) >>= fun _ => pure true := by
  simp only [SM_DT_TCR_Experiment, problem_seedGen, pure_bind]
  rw [run_coinFlip]
  simp [coinFlip, problem_eval]

end SMDTTCRTest
