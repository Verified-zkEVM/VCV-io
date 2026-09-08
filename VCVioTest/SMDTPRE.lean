/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE

/-!
# End-to-end canaries for SM-DT-PRE

The pins in `HardnessAssumptions/TweakableHash/SMDTPRE.lean` stop at the challenge oracle's `run`;
these run the whole game, winning condition included. Between them they exercise the three parts of
`SM_DT_PRE_Experiment` no oracle pin reaches: that an accepted query's sampled message is recorded
where the winning condition looks for it, that the index lookup resolves against the challenge
history, and that a rejected query leaves nothing to invert.

The challenge oracle draws its own message, so the subspace is a one-element type whose
`SampleableType` instance is written out rather than inferred. That makes the draw reduce, and the
transcripts below are then equations between `pure`s rather than statements about `support`.

Because the target cap is one, append order is unobservable here; `SMDTTCR.lean` carries the order
canaries for the SM-TCR side, whose challenge history is built by the same `TweakFresh` discipline.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace SMDTPRETest

/-! ## A collapsing tweakable hash on a one-element subspace -/

inductive Seed
  | only

inductive Digest
  | zero
  deriving DecidableEq

instance : SampleableType Seed where
  selectElem := pure .only
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

instance : SampleableType Digest where
  selectElem := pure .zero
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

@[simp] lemma uniformSample_seed : ($ᵗ Seed : ProbComp Seed) = pure .only := rfl

@[simp] lemma uniformSample_digest : ($ᵗ Digest : ProbComp Digest) = pure .zero := rfl

def hash : TweakableHash Seed Bool Bool Bool where
  seedGen := $ᵗ Seed
  eval _ _ _ := false

def collection : TweakableHashCollection Unit Seed Bool Bool where
  Msg _ := Bool
  eval _ _ _ _ := false

def problem : SM_DT_PRE_Problem Unit Seed Bool Bool Digest Bool where
  th := hash
  emb _ := false
  emb_injective := fun a b _ => by cases a; cases b; rfl
  thColl := collection
  numTargets := 1

@[simp] lemma problem_seedGen : problem.th.seedGen = pure .only := rfl

/-! ## Queries -/

abbrev Specs := unifSpec + (SM_DT_PRE_challengeSpec Bool Bool + collectionSpec problem.thColl)

/-- Query the challenge oracle at `tweak`; the oracle picks the message. -/
def challenge (tweak : Bool) : OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inl tweak)))

/-- Query the collection oracle on its sole member at `(tweak, message)`. -/
def collectionQuery (tweak : Bool) (message : problem.thColl.Msg ()) :
    OracleComp Specs (Option Bool) :=
  liftM (Specs.query (.inr (.inr ⟨(), tweak, message⟩)))

/-! ## Adversaries -/

/-- Place one target, then invert it. -/
def challengeOnly : SM_DT_PRE_Adversary problem where
  State := Unit
  choose := do
    let _ ← challenge true
    return ()
  invert _ _ := pure (0, .zero)

/-- Spend the tweak on the collection oracle before challenging at it. -/
def collectionThenChallenge : SM_DT_PRE_Adversary problem where
  State := Unit
  choose := do
    let _ ← collectionQuery true false
    let _ ← challenge true
    return ()
  invert _ _ := pure (0, .zero)

/-! ## Transcripts -/

private lemma run_challengeOnly :
    (simulateQ (SM_DT_PRE_oracles problem .only) challengeOnly.choose).run ([], []) =
      pure ((), ([(true, Digest.zero)], [])) := by
  rfl

private lemma run_collectionThenChallenge :
    (simulateQ (SM_DT_PRE_oracles problem .only) collectionThenChallenge.choose).run ([], []) =
      pure ((), ([], [true])) := by
  rfl

/-! ## Verdicts -/

/-- A target placed through the challenge oracle and inverted at its own index wins. -/
theorem win_challengeOnly : SM_DT_PRE_Experiment challengeOnly = pure true := by
  simp only [SM_DT_PRE_Experiment, problem_seedGen, pure_bind]
  rw [run_challengeOnly]
  simp [challengeOnly]

/-- Reaching a tweak through the collection oracle first makes the later challenge query at that
tweak be rejected, so nothing is drawn and index `0` is out of range. -/
theorem lose_collectionThenChallenge :
    SM_DT_PRE_Experiment collectionThenChallenge = pure false := by
  simp only [SM_DT_PRE_Experiment, problem_seedGen, pure_bind]
  rw [run_collectionThenChallenge]
  simp [collectionThenChallenge]

end SMDTPRETest
