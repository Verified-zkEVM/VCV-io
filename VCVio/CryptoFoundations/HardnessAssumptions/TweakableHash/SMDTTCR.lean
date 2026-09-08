/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function, distinct-tweak, multi-target target-collision resistance (SM-DT-TCR)

The adversary first selects up to `numTargets` targets through an oracle evaluating the tweakable
hash at a public seed it does not know, then learns the seed and must collide with one of the images
it received. It may evaluate the other members of the collection throughout, through
`collectionOracle`.

Shortened to `SM-TCR` in the prose below; the declaration names keep the full label.

The seed is sampled by `SM_DT_TCR_Experiment` and passed only to `SM_DT_TCR_Adversary.forge`; it
never reaches `SM_DT_TCR_Adversary.choose`. The two phases are separate fields at different types,
`OracleComp (SM_DT_TCR_challengeSpec …)` against `ProbComp`, so "the oracle is removed once the seed
is revealed" is a typing fact and not a runtime convention: `forge` has no oracle to query.

`numTargets` bounds the accepted challenge queries and is the only query bound the game carries. See
`TweakableHash.collectionOracle` for why the tweak restrictions are enforced in the oracles rather
than in the winning condition.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6.
- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1 Def. 3.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a `(tweak, message)` pair, and the response is
`Option Y`, with `none` marking a rejected query. -/
abbrev SM_DT_TCR_challengeSpec (Tweak M Y : Type) : OracleSpec (Tweak × M) :=
  (Tweak × M) →ₒ Option Y

/-- An SM-TCR problem: the tweakable hash under attack, the collection its other members form, and
the bound on the number of targets the adversary may select. -/
structure SM_DT_TCR_Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose target-collision resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The cap on accepted challenge-oracle queries. -/
  numTargets : ℕ

/-- The stand-alone SM-TCR problem, at the empty collection: the collection oracle's query type is
uninhabited, so the adversary has only the challenge oracle. -/
def SM_DT_TCR_Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (numTargets : ℕ) :
    SM_DT_TCR_Problem Empty PkSeed Tweak M Y where
  th := th
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-TCR game: the challenge history of accepted
`(tweak, message)` targets, and the list of tweaks spent on the collection oracle. -/
abbrev SM_DT_TCR_State (Tweak M : Type) : Type := List (Tweak × M) × List Tweak

/-- An SM-TCR adversary. `choose` selects targets through the challenge oracle, may evaluate the
rest of the collection, and has private uniform randomness without access to the public seed;
`forge` receives the seed and the private state, and has no oracle. -/
structure SM_DT_TCR_Adversary (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Select targets through the challenge oracle, with private uniform randomness and collection
  access. The public seed is not an input. -/
  choose : OracleComp
    (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl)) State
  /-- Given the revealed public seed, name a target index and a colliding message. -/
  forge : State → PkSeed → ProbComp (ℕ × M)

/-- The challenge oracle at a public seed, answering with the hash of the queried `(tweak, message)`
pair and recording that pair in the challenge history. A query is rejected with `none` when the
target cap is reached, when its tweak already occurs in the challenge history, or when its tweak has
been spent on the collection oracle; a rejected query leaves the state untouched.

Accepted queries are appended, so the history is in issue order and its `j`-th entry is the `j`-th
target. -/
def SM_DT_TCR_challengeOracle [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (SM_DT_TCR_challengeSpec Tweak M Y) (StateT (SM_DT_TCR_State Tweak M) ProbComp) :=
  fun tm => do
    let (qsChal, twsColl) ← get
    if prob.numTargets ≤ qsChal.length ∨ ¬ TweakFresh Prod.fst qsChal twsColl tm.1 then
      return none
    else
      set (qsChal ++ [tm], twsColl)
      return some (prob.th.eval pk tm.1 tm.2)

/-- Both oracles of the SM-TCR game over the shared state, at a public seed. -/
def SM_DT_TCR_oracles [DecidableEq Tweak] (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) :
    QueryImpl (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.thColl))
      (StateT (SM_DT_TCR_State Tweak M) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM_DT_TCR_State Tweak M) ProbComp) +
    (SM_DT_TCR_challengeOracle prob pk +
      collectionOracle (Q := Tweak × M) Prod.fst prob.thColl pk)

/-- The SM-TCR experiment. The public seed is sampled, the first phase runs against both oracles
without it, the second phase runs with it and without them, and the adversary wins by naming a
recorded target `j` and a message colliding with — and differing from — the `j`-th recorded message.
An index outside the challenge history loses. -/
noncomputable def SM_DT_TCR_Experiment [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) :
    ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, qsChal, _) ← (simulateQ (SM_DT_TCR_oracles prob pk) adv.choose).run ([], [])
  let (j, m) ← adv.forge st pk
  match qsChal[j]? with
  | none => return false
  | some (t, mj) => return decide (m ≠ mj ∧ prob.th.eval pk t m = prob.th.eval pk t mj)

/-- The SM-TCR advantage of an adversary. -/
noncomputable def SM_DT_TCR_Advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_TCR_Experiment adv]

/-! ## Basic properties and conventions -/

variable [DecidableEq Tweak] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} {pk : PkSeed}
  {t : Tweak} {m : M} {qsChal : List (Tweak × M)} {twsColl : List Tweak}

/-- A query with a tweak fresh to both histories, below the target cap, is answered with the hash
and appended to the end of the challenge history. -/
theorem SM_DT_TCR_challengeOracle_run_of_fresh (hlen : qsChal.length < prob.numTargets)
    (hfresh : TweakFresh Prod.fst qsChal twsColl t) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (some (prob.th.eval pk t m), (qsChal ++ [(t, m)], twsColl)) := by
  simp [SM_DT_TCR_challengeOracle, Nat.not_le.mpr hlen, hfresh]

/-- A query reusing a tweak already in the challenge history is rejected, and the state is
unchanged. -/
theorem SM_DT_TCR_challengeOracle_run_of_reused (m' : M) (hmem : (t, m') ∈ qsChal) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  have hres : TweakReserved Prod.fst qsChal t := ⟨(t, m'), hmem, rfl⟩
  simp [SM_DT_TCR_challengeOracle, TweakFresh, hres]

/-- A query at the target cap is rejected, and the state is unchanged. -/
theorem SM_DT_TCR_challengeOracle_run_of_full (hlen : prob.numTargets ≤ qsChal.length) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  simp [SM_DT_TCR_challengeOracle, hlen]

/-- A query at a tweak already spent on the collection oracle is rejected, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem SM_DT_TCR_challengeOracle_run_of_collection_clash (hmem : t ∈ twsColl) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  simp [SM_DT_TCR_challengeOracle, TweakFresh, hmem]

end TweakableHash
