/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function, distinct-tweak, multi-target decisional second-preimage resistance (SM-DT-DSPR)

The adversary first selects up to `numTargets` targets through an oracle evaluating the tweakable
hash at a public seed it does not know, then learns the seed, names one of its targets, and
predicts whether that target has a second preimage. It may evaluate the other members of the
collection throughout, through `collectionOracle`. This is the same two-phase shape as SM-DT-TCR,
with the forging phase replaced by a decisional guess:
`SM_DT_DSPR_Adversary.guess : State → PkSeed → ProbComp (ℕ × Bool)` returns a target index and a
predicted bit rather than a colliding message.

Shortened to `SM-DSPR` in the prose below; the declaration names keep the full label.

`numTargets` bounds the accepted challenge queries and is the only query bound the game carries,
enforced by rejecting an over-cap or tweak-reusing query with `none` — the same discipline
`SM_DT_TCR_challengeOracle` uses. See `TweakableHash.collectionOracle` for why the tweak
restrictions are enforced in the oracles rather than in the winning condition.

The security quantity is **not** raw prediction success. `SM_DT_DSPR_SPExperiment` is the source
proof's `SPprob` baseline: it runs the same adversary, including target selection and the guess
phase, but accepts exactly when the named target has a second preimage, independently of the
guessed bit. `SM_DT_DSPR_Advantage` is the truncated difference `Pr[DSPR] - Pr[SPprob]` in `ℝ≥0∞` —
the same triple `SM_DT_DSPR_SourceFinalValidity` already defines, reused unchanged here because the
baseline is a property of what counts as winning, not of how a rejected query is handled.
`SecondPreimageExists` and its `Decidable` instance are imported from `SMDTDSPRFinalValidity`, not
restated.

HK22 Definition 6 and BDHMS24 Figures 8–9 both present SM-DT-DSPR only with final-validity
semantics: distinctness of target tweaks is a post-hoc `DIST` conjunct checked once after the
guess, not a per-query rejection. Neither paper, nor DKKW (whose §3.1 supplies the
rejection-on-arrival discipline this library already uses for SM-DT-TCR and SM-DT-PRE), presents a
rejection-on-arrival decisional second-preimage game — there is no numbered definition to
transcribe here. This file applies that same rejection discipline to HK22's decisional
second-preimage game, for symmetry with its final-validity sibling; the game below is new to this
library, not a transcription of a numbered definition in the cited sources.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 6.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 8 and Fig. 9.
- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1, for the rejection-on-arrival
  discipline applied here; DKKW does not present a decisional second-preimage game.
-/

public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a `(tweak, message)` pair, and the response is
`Option Y`, with `none` marking a rejected query. -/
abbrev SM_DT_DSPR_challengeSpec (Tweak M Y : Type) : OracleSpec (Tweak × M) :=
  (Tweak × M) →ₒ Option Y

/-- An SM-DT-DSPR problem: the tweakable hash under attack, the collection its other members form,
and the bound on the number of targets the adversary may select. -/
structure SM_DT_DSPR_Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose second-preimage structure is being predicted. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The cap on accepted challenge-oracle queries. -/
  numTargets : ℕ

/-- The stand-alone SM-DT-DSPR problem, at the empty collection: the collection oracle's query type
is uninhabited, so the adversary has only the challenge oracle. -/
@[expose] def SM_DT_DSPR_Problem.standalone
    (th : TweakableHash PkSeed Tweak M Y) (numTargets : ℕ) :
    SM_DT_DSPR_Problem Empty PkSeed Tweak M Y where
  th := th
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-DT-DSPR game: the challenge history of
accepted `(tweak, message)` targets, and the list of tweaks spent on the collection oracle. -/
abbrev SM_DT_DSPR_State (Tweak M : Type) : Type := List (Tweak × M) × List Tweak

/-- An SM-DT-DSPR adversary. `choose` selects targets through the challenge oracle, may evaluate
the rest of the collection, and has private uniform randomness without access to the public seed;
`guess` receives the seed and the private state, and has no oracle. It names a target index and
predicts whether that target has a second preimage. -/
structure SM_DT_DSPR_Adversary (prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `guess`. -/
  State : Type
  /-- Select targets through the challenge oracle, with private uniform randomness and collection
  access. The public seed is not an input. -/
  choose : OracleComp
    (unifSpec + (SM_DT_DSPR_challengeSpec Tweak M Y + collectionSpec prob.thColl)) State
  /-- Given the revealed public seed, name a target index and predict whether it has a second
  preimage. -/
  guess : State → PkSeed → ProbComp (ℕ × Bool)

/-- The challenge oracle at a public seed, answering with the hash of the queried `(tweak, message)`
pair and recording that pair in the challenge history. A query is rejected with `none` when the
target cap is reached, when its tweak already occurs in the challenge history, or when its tweak has
been spent on the collection oracle; a rejected query leaves the state untouched.

Accepted queries are appended, so the history is in issue order and its `j`-th entry is the `j`-th
target. -/
@[expose] def SM_DT_DSPR_challengeOracle [DecidableEq Tweak]
    (prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (SM_DT_DSPR_challengeSpec Tweak M Y) (StateT (SM_DT_DSPR_State Tweak M) ProbComp) :=
  fun tm => do
    let (qsChal, twsColl) ← get
    if prob.numTargets ≤ qsChal.length ∨ ¬ TweakFresh Prod.fst qsChal twsColl tm.1 then
      return none
    else
      set (qsChal ++ [tm], twsColl)
      return some (prob.th.eval pk tm.1 tm.2)

/-- Both oracles of the SM-DT-DSPR game over the shared state, at a public seed. -/
@[expose] def SM_DT_DSPR_oracles [DecidableEq Tweak] (prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) :
    QueryImpl (unifSpec + (SM_DT_DSPR_challengeSpec Tweak M Y + collectionSpec prob.thColl))
      (StateT (SM_DT_DSPR_State Tweak M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM_DT_DSPR_State Tweak M) ProbComp) +
    (SM_DT_DSPR_challengeOracle prob pk +
      collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk)

/-- The SM-DT-DSPR experiment. The public seed is sampled, the first phase runs against both
oracles without it, the second phase runs with it and without them, and the adversary wins by
naming a recorded target `j` and correctly predicting whether it has a second preimage. An index
outside the challenge history loses. -/
@[expose] noncomputable def SM_DT_DSPR_Experiment [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, qsChal, _) ← (simulateQ (SM_DT_DSPR_oracles prob pk) adv.choose).run ([], [])
  let (j, b) ← adv.guess st pk
  match qsChal[j]? with
  | none => return false
  | some (t, m) => return decide (SecondPreimageExists prob.th pk t m ↔ b = true)

/-- The source proof's `SPprob` baseline. It runs exactly the same adversary and uses the same
named index, but ignores the guessed bit and accepts iff that target has a second preimage. -/
@[expose] noncomputable def SM_DT_DSPR_SPExperiment [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, qsChal, _) ← (simulateQ (SM_DT_DSPR_oracles prob pk) adv.choose).run ([], [])
  let (j, _) ← adv.guess st pk
  match qsChal[j]? with
  | none => return false
  | some (t, m) => return decide (SecondPreimageExists prob.th pk t m)

/-- Raw SM-DT-DSPR prediction success probability. Kept separate from the security advantage so the
baseline subtraction cannot be accidentally omitted at a call site. -/
@[expose] noncomputable def SM_DT_DSPR_Success [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_DSPR_Experiment adv]

/-- The `SPprob` baseline success probability. -/
@[expose] noncomputable def SM_DT_DSPR_SPProbability [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_DSPR_SPExperiment adv]

/-- SM-DT-DSPR advantage: the `ℝ≥0∞` truncated difference `Pr[DSPR] - Pr[SPprob]`. -/
@[expose] noncomputable def SM_DT_DSPR_Advantage [Fintype M] [DecidableEq Tweak] [DecidableEq M]
    [DecidableEq Y] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y}
    (adv : SM_DT_DSPR_Adversary prob) : ℝ≥0∞ :=
  SM_DT_DSPR_Success adv - SM_DT_DSPR_SPProbability adv

/-! ## Basic properties and conventions -/

variable [DecidableEq Tweak] {prob : SM_DT_DSPR_Problem ι PkSeed Tweak M Y} {pk : PkSeed}
  {t : Tweak} {m : M} {qsChal : List (Tweak × M)} {twsColl : List Tweak}

/-- A query with a tweak fresh to both histories, below the target cap, is answered with the hash
and appended to the end of the challenge history. -/
theorem SM_DT_DSPR_challengeOracle_run_of_fresh (hlen : qsChal.length < prob.numTargets)
    (hfresh : TweakFresh Prod.fst qsChal twsColl t) :
    (SM_DT_DSPR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (some (prob.th.eval pk t m), (qsChal ++ [(t, m)], twsColl)) := by
  simp [SM_DT_DSPR_challengeOracle, Nat.not_le.mpr hlen, hfresh]

/-- A query reusing a tweak already in the challenge history is rejected, and the state is
unchanged. -/
theorem SM_DT_DSPR_challengeOracle_run_of_reused (m' : M) (hmem : (t, m') ∈ qsChal) :
    (SM_DT_DSPR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  have hres : TweakReserved Prod.fst qsChal t := ⟨(t, m'), hmem, rfl⟩
  simp [SM_DT_DSPR_challengeOracle, TweakFresh, hres]

/-- A query at the target cap is rejected, and the state is unchanged. -/
theorem SM_DT_DSPR_challengeOracle_run_of_full (hlen : prob.numTargets ≤ qsChal.length) :
    (SM_DT_DSPR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  simp [SM_DT_DSPR_challengeOracle, hlen]

/-- A query at a tweak already spent on the collection oracle is rejected, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem SM_DT_DSPR_challengeOracle_run_of_collection_clash (hmem : t ∈ twsColl) :
    (SM_DT_DSPR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  simp [SM_DT_DSPR_challengeOracle, TweakFresh, hmem]

end TweakableHash
