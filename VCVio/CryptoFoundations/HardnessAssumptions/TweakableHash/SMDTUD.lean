/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append
public import ToMathlib.Data.ENNReal.AbsDiff

/-!
# Single-function, distinct-tweak, multi-target undetectability (SM-DT-UD)

SM-DT-UD asks an adversary to distinguish sampled images of one tweakable hash from samples of an
explicit output distribution. The public seed is sampled by the experiment and withheld while the
adversary selects target tweaks through the challenge oracle and evaluates the shared hash
collection. The seed is revealed only after those oracles have been removed, and the adversary then
names the world it was answered from.

Shortened to `SM-UD` in the prose below; the declaration names keep the full label.

In the real world, a challenge at `t` samples `x ← inputGen` from the subspace `M'` and returns
`th.eval pk t (emb x)`. In the ideal world it returns `y ← outputGen`. The two worlds differ in
nothing else: `SM_DT_UD_response` is the only world-indexed definition, and the tweak discipline,
the recording, and the refusal test are shared.

The tweak discipline is enforced on arrival. The challenge oracle answers `Option Y` and returns
`none` — the source's `⊥` — when the target cap is reached, when the queried tweak already occurs
in the challenge history, or when it has been spent on the collection oracle; a refused query
leaves the state untouched and **draws nothing**, so refusal consumes no randomness in either
world. That last point is what makes the two worlds' refusal behaviour literally the same term, and
it is pinned by `SM_DT_UD_challengeOracle_run_of_refused`. See `TweakableHash.collectionOracle` for
why the restrictions live in the oracles rather than in the winning condition, and
`TweakableHash.SM_DT_UD_SourceFinalValidity` for the sticky-monitor presentation of the same
notion, which answers every query and checks the discipline once at the end.

`numTargets` bounds the accepted challenge queries and is the only query bound the game carries. It
is the source's `p`, the number of classical challenge-oracle queries; the source's `q`, the number
of queries to the hash function itself, is a quantity of the random-oracle analysis in which `Th`
is an oracle rather than a function, and is not a parameter of this game.

The subspace the hidden input is drawn from is carried as its own type `M'` together with an
injective `emb : M' → M`, matching `TweakableHash.SM_DT_PRE_Problem`. A subspace carved out of `M`
by a predicate is the case `M' := Subtype p`, `emb := Subtype.val` (`Subtype.val_injective`); the
unrestricted notion is recovered exactly at `M' := M`, `emb := id` (`Function.injective_id`), so
the parameterization costs no generality. It buys the ability to state bounds in `|M'|` rather than
`|M|`: `SM_DT_UD_Problem.HasUniformInputs` fixes `inputGen` to the uniform distribution on the
subspace, which is what a quantitative bound of the form `q / |M'|` needs, and
`SM_DT_UD_Problem.HasUniformOutputs` fixes the ideal response to the uniform distribution on `Y`.

The security quantity is oriented: `SM_DT_UD_DirectedAdvantage` is the signed real gap
`Pr[real = true] - Pr[ideal = true]`. It can be negative, so swapping the real and ideal worlds is
observable. `SM_DT_UD_AbsoluteAdvantage` separately provides the symmetric `ℝ≥0∞` magnitude used by
orientation-independent bounds, with a proved bridge between the two views.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1 Def. 5.
- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 4 and Def. 7.
- Barbosa, Dupressoir, Grégoire, Hülsing, Meijers and Strub, *Machine-Checked Security for XMSS as
  in RFC 8391 and SPHINCS+*, [ePrint 2023/408](https://eprint.iacr.org/2023/408), Figs. 5, 6 and 9.
-/

public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M M' Y : Type}

/-! ## The game -/

/-- Which response distribution the challenge oracle uses. -/
inductive SM_DT_UD_World
  /-- Sample a hidden input and evaluate the attacked tweakable hash. -/
  | real
  /-- Sample directly from the problem's output distribution. -/
  | ideal
deriving DecidableEq, Repr

/-- The challenge oracle's signature: a query is a tweak alone, and the response is `Option Y`,
with `none` marking a refused query. -/
abbrev SM_DT_UD_challengeSpec (Tweak Y : Type) : OracleSpec Tweak := Tweak →ₒ Option Y

/-- An SM-UD problem: attacked hash, the subspace its hidden inputs are drawn from, explicit real
and ideal sampling distributions, shared collection, and target cap. -/
structure SM_DT_UD_Problem (ι PkSeed Tweak M M' Y : Type) where
  /-- The tweakable hash whose sampled images should be indistinguishable from `outputGen`. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The map into `M` of the subspace the real challenge world samples from. -/
  emb : M' → M
  /-- `emb` identifies `M'` with a subset of `M`. This is what makes the oracle's uniform draw on
  `M'` a uniform draw on a subset of `M`: under a non-injective `emb` the law of `emb x` is the
  pushforward of the uniform distribution, which is not uniform on the image. No definition or
  proof in this module uses the field; it is a side condition carried for the reductions that state
  bounds in `|M'|`, as in `TweakableHash.SM_DT_PRE_Problem`. -/
  emb_injective : Function.Injective emb
  /-- Distribution of hidden inputs in the real challenge world, on the subspace `M'`. -/
  inputGen : ProbComp M'
  /-- Distribution of direct challenge outputs in the ideal world. -/
  outputGen : ProbComp Y
  /-- The rest of the collection, evaluable by the adversary at the game's hidden seed. -/
  thColl : TweakableHashCollection ι PkSeed Tweak Y
  /-- The cap on accepted challenge-oracle queries. -/
  numTargets : ℕ

/-- The property on `inputGen` that a quantitative bound in `|M'|` requires: the hidden input is
uniform on the subspace, with full support. Keeping it separate from the game permits a more
general definition while making the reduction's additional hypothesis explicit.

Uniformity is asked of the subspace rather than of `M`, which is what lets a bound of the form
`q / |M'|` be stated at a strict `M' ⊊ M`. -/
@[expose] def SM_DT_UD_Problem.HasUniformInputs [SampleableType M']
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) : Prop :=
  prob.inputGen = $ᵗ M'

/-- The ideal challenge distribution is uniform on the output space. Together with
`SM_DT_UD_Problem.HasUniformInputs`, this selects the challenge distributions of the standard
subspace-indexed SM-UD experiment while leaving the abstract game available for other hybrids.
The source-final-validity presentation carries the same pair of predicates as
`TweakableHash.SM_DT_UD_SourceFinalValidity.Problem.HasUniformOutputs`. -/
def SM_DT_UD_Problem.HasUniformOutputs [SampleableType Y]
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) : Prop :=
  prob.outputGen = $ᵗ Y

/-- The stand-alone SM-UD problem, at the empty collection: the collection oracle's query type is
uninhabited, so the adversary has only the challenge oracle. -/
@[expose] def SM_DT_UD_Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (emb : M' → M)
    (emb_injective : Function.Injective emb)
    (inputGen : ProbComp M') (outputGen : ProbComp Y) (numTargets : ℕ) :
    SM_DT_UD_Problem Empty PkSeed Tweak M M' Y where
  th := th
  emb := emb
  emb_injective := emb_injective
  inputGen := inputGen
  outputGen := outputGen
  thColl := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-UD game: the challenge history of accepted
target tweaks, and the list of tweaks spent on the collection oracle. The challenge history is
tweaks alone, since the winning condition is the adversary's own bit and needs no payload. -/
abbrev SM_DT_UD_State (Tweak : Type) : Type := List Tweak × List Tweak

/-- An SM-UD adversary, split exactly at the public-seed reveal. `pick` selects target tweaks
through the challenge oracle, may evaluate the rest of the collection, and has private uniform
randomness without access to the seed; `distinguish` receives the seed and the private state, and
has no oracle. -/
structure SM_DT_UD_Adversary (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) where
  /-- Private state carried from `pick` to `distinguish`. -/
  State : Type
  /-- Select target tweaks through the challenge oracle, with private uniform randomness and
  collection access. The public seed is not an input. -/
  pick : OracleComp
    (unifSpec + (SM_DT_UD_challengeSpec Tweak Y + collectionSpec prob.thColl)) State
  /-- After the seed is revealed and both oracles are removed, return the distinguishing bit. -/
  distinguish : State → PkSeed → ProbComp Bool

/-- One challenge response. Only this distribution differs between the real and ideal worlds. -/
@[expose] def SM_DT_UD_response (world : SM_DT_UD_World)
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) (t : Tweak) : ProbComp Y :=
  match world with
  | .real => do
      let x ← prob.inputGen
      return prob.th.eval pk t (prob.emb x)
  | .ideal => prob.outputGen

/-- The challenge oracle at a public seed, answering with a sample of the queried world's response
distribution and recording the queried tweak in the challenge history. A query is refused with
`none` when the target cap is reached, when its tweak already occurs in the challenge history, or
when its tweak has been spent on the collection oracle.

The refusal test is read off the state *before* anything is drawn, and the refusing branch is a
`pure`: a refused query leaves the state untouched and consumes no randomness. That asymmetry
between the two branches is deliberate and load-bearing. If refusal drew from the response
distribution, it would draw a different amount in the two worlds whenever `inputGen` and
`outputGen` differ in length, and the advantage would then charge the adversary for randomness it
never observed.

Accepted queries are appended, so the history is in issue order and its `j`-th entry is the `j`-th
target. -/
@[expose] def SM_DT_UD_challengeOracle [DecidableEq Tweak] (world : SM_DT_UD_World)
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (SM_DT_UD_challengeSpec Tweak Y) (StateT (SM_DT_UD_State Tweak) ProbComp) :=
  fun t => do
    let s ← get
    if prob.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then
      return none
    else
      let y ← (SM_DT_UD_response world prob pk t :
        StateT (SM_DT_UD_State Tweak) ProbComp Y)
      set (s.1 ++ [t], s.2)
      return some y

/-- Both oracles of the SM-UD game over the shared state, at a public seed. The challenge history
is tweaks alone, so the collection oracle reads it through `id`. -/
@[expose] def SM_DT_UD_oracles [DecidableEq Tweak] (world : SM_DT_UD_World)
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (unifSpec + (SM_DT_UD_challengeSpec Tweak Y + collectionSpec prob.thColl))
      (StateT (SM_DT_UD_State Tweak) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM_DT_UD_State Tweak) ProbComp) +
    (SM_DT_UD_challengeOracle world prob pk +
      collectionOracle (Q := Tweak) id prob.thColl pk)

/-- The SM-UD experiment in one world. The seed is sampled, the first phase runs against both
oracles without it, the second phase runs with it and without them, and the experiment outputs the
adversary's bit. The tweak discipline is already enforced by the oracles, so the outcome reads the
adversary's bit and nothing else. -/
@[expose] noncomputable def SM_DT_UD_Experiment [DecidableEq Tweak] (world : SM_DT_UD_World)
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (privateState, _) ← (simulateQ (SM_DT_UD_oracles world prob pk) adv.pick).run ([], [])
  adv.distinguish privateState pk

/-- Success probability when challenges are sampled hash images. -/
@[expose] noncomputable def SM_DT_UD_RealSuccess [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_UD_Experiment .real adv]

/-- Success probability when challenges are sampled directly from `outputGen`. -/
@[expose] noncomputable def SM_DT_UD_IdealSuccess [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_UD_Experiment .ideal adv]

/-- SM-UD advantage: the directed signed gap from the real world to the ideal world. -/
@[expose] noncomputable def SM_DT_UD_DirectedAdvantage [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) : ℝ :=
  (SM_DT_UD_RealSuccess adv).toReal - (SM_DT_UD_IdealSuccess adv).toReal

/-- Orientation-independent magnitude of the SM-UD advantage in `ℝ≥0∞`. This is deliberately
separate from the game's signed `SM_DT_UD_DirectedAdvantage`. -/
@[expose] noncomputable def SM_DT_UD_AbsoluteAdvantage [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) : ℝ≥0∞ :=
  ENNReal.absDiff (SM_DT_UD_RealSuccess adv) (SM_DT_UD_IdealSuccess adv)

/-- The `ℝ≥0∞` absolute gap is exactly the absolute value of the directed advantage. -/
theorem SM_DT_UD_absoluteAdvantage_toReal_eq_abs_directedAdvantage [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    (SM_DT_UD_AbsoluteAdvantage adv).toReal = |SM_DT_UD_DirectedAdvantage adv| := by
  exact ENNReal.absDiff_toReal probOutput_ne_top probOutput_ne_top

/-- Forgetting orientation gives a sound upper bound on the directed advantage. -/
theorem SM_DT_UD_directedAdvantage_le_absoluteAdvantage_toReal [DecidableEq Tweak]
    {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_UD_Adversary prob) :
    SM_DT_UD_DirectedAdvantage adv ≤ (SM_DT_UD_AbsoluteAdvantage adv).toReal := by
  rw [SM_DT_UD_absoluteAdvantage_toReal_eq_abs_directedAdvantage]
  exact le_abs_self _

/-! ## The accepted branches

Each world's accepted response is pinned separately, so a swap of the two is a broken proof rather
than a silent change of meaning. -/

section AcceptedBranches

variable [DecidableEq Tweak] {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} {pk : PkSeed}
  {t : Tweak} {qsChal twsColl : List Tweak}

/-- In the real world, a query with a tweak fresh to both histories, below the target cap, draws a
hidden input from the subspace and answers with the hash of its embedding. The tweak is appended to
the end of the challenge history. -/
theorem SM_DT_UD_challengeOracle_run_of_fresh_real (hlen : qsChal.length < prob.numTargets)
    (hfresh : TweakFresh id qsChal twsColl t) :
    (SM_DT_UD_challengeOracle .real prob pk t).run (qsChal, twsColl) =
      (fun x => (some (prob.th.eval pk t (prob.emb x)), (qsChal ++ [t], twsColl))) <$>
        prob.inputGen := by
  simp [SM_DT_UD_challengeOracle, SM_DT_UD_response, Nat.not_le.mpr hlen, hfresh,
    Functor.map_map]

/-- In the ideal world, the same query answers with a sample of `outputGen`, independently of the
tweakable hash and of the subspace. -/
theorem SM_DT_UD_challengeOracle_run_of_fresh_ideal (hlen : qsChal.length < prob.numTargets)
    (hfresh : TweakFresh id qsChal twsColl t) :
    (SM_DT_UD_challengeOracle .ideal prob pk t).run (qsChal, twsColl) =
      (fun y => (some y, (qsChal ++ [t], twsColl))) <$> prob.outputGen := by
  simp [SM_DT_UD_challengeOracle, SM_DT_UD_response, Nat.not_le.mpr hlen, hfresh,
    Functor.map_map]

end AcceptedBranches

/-! ## The refusing branch

Refusal is world-independent and draws nothing. The general statement is
`SM_DT_UD_challengeOracle_run_of_refused`, whose right-hand side is a `pure` at an arbitrary world;
the three named causes are its corollaries. -/

section RefusingBranch

variable [DecidableEq Tweak] {world : SM_DT_UD_World}
  {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} {pk : PkSeed} {t : Tweak}
  {qsChal twsColl : List Tweak}

/-- A refused query returns `none`, leaves the state untouched, and draws nothing — in either
world, from the same term.

This is the game's central convention and no build gate can see it. Both worlds are covered by one
statement because `world` is universally quantified, and the right-hand side is a `pure`, so no
sample of `SM_DT_UD_response` is taken. Were the draw hoisted above the refusal test, the two
worlds would consume different amounts of randomness on a refused query while returning the same
`none`, and `SM_DT_UD_DirectedAdvantage` would no longer measure what the adversary can observe. -/
theorem SM_DT_UD_challengeOracle_run_of_refused
    (hrefused : prob.numTargets ≤ qsChal.length ∨ ¬ TweakFresh id qsChal twsColl t) :
    (SM_DT_UD_challengeOracle world prob pk t).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  simp [SM_DT_UD_challengeOracle, hrefused]

/-- A query reusing a tweak already in the challenge history is refused, and the state is
unchanged. -/
theorem SM_DT_UD_challengeOracle_run_of_reused (hmem : t ∈ qsChal) :
    (SM_DT_UD_challengeOracle world prob pk t).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) :=
  SM_DT_UD_challengeOracle_run_of_refused (Or.inr fun hfresh => hfresh.1 ⟨t, hmem, rfl⟩)

/-- A query at the target cap is refused, and the state is unchanged. -/
theorem SM_DT_UD_challengeOracle_run_of_full (hlen : prob.numTargets ≤ qsChal.length) :
    (SM_DT_UD_challengeOracle world prob pk t).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) :=
  SM_DT_UD_challengeOracle_run_of_refused (Or.inl hlen)

/-- A query at a tweak already spent on the collection oracle is refused, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem SM_DT_UD_challengeOracle_run_of_collection_clash (hmem : t ∈ twsColl) :
    (SM_DT_UD_challengeOracle world prob pk t).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) :=
  SM_DT_UD_challengeOracle_run_of_refused (Or.inr fun hfresh => hfresh.2 hmem)

end RefusingBranch

/-! ## Issue order, and the collection half

The two facts a single query cannot see: that accepted challenge tweaks are recorded in issue
order, and that repeating a collection-only tweak is accepted. -/

section IssueOrder

variable [DecidableEq Tweak] {world : SM_DT_UD_World}
  {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} {pk : PkSeed} {t₁ t₂ : Tweak}

/-- Two accepted challenge queries at distinct tweaks record them in issue order, and each accepted
query takes exactly one sample of its world's response distribution, in that order.

Stated over two queries because the append order is invisible at one: consing instead of appending
would give `[t₂, t₁]` here and misattribute every target index, while leaving every single-query
statement true. Stating it at an arbitrary `world` covers both worlds at once, and keeping both
draws on the right-hand side pins that the first accepted query samples even though its answer is
discarded. -/
theorem SM_DT_UD_challengeOracle_run_two_queries (hne : t₁ ≠ t₂) (hcap : 2 ≤ prob.numTargets) :
    ((SM_DT_UD_challengeOracle world prob pk t₁).run ([], []) >>= fun r =>
        (SM_DT_UD_challengeOracle world prob pk t₂).run r.2) =
      (SM_DT_UD_response world prob pk t₁ >>= fun _ =>
        (fun y => (some y, ([t₁, t₂], ([] : List Tweak)))) <$>
          SM_DT_UD_response world prob pk t₂) := by
  have h₁ : ¬ prob.numTargets ≤ 0 := by omega
  have h₂ : ¬ prob.numTargets ≤ 1 := by omega
  simp [SM_DT_UD_challengeOracle, TweakFresh, TweakReserved, h₁, h₂, hne.symm,
    StateT.run_bind, Functor.map_map]

end IssueOrder

section CollectionHalf

variable [DecidableEq Tweak] {world : SM_DT_UD_World}
  {prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y} {pk : PkSeed}
  {qsChal twsColl : List Tweak}

/-- Repeating a collection tweak is accepted through the game's own oracle bundle: querying the
same collection member at the same tweak twice in a row is answered both times, and both
occurrences are appended. Only disjointness from the target tweaks is required, not distinctness
among the collection tweaks themselves.

Stated through `SM_DT_UD_oracles` rather than `collectionOracle` alone, so it fails if the game
wires up a collection oracle that enforces self-distinctness. -/
theorem SM_DT_UD_oracles_run_collection_repeated (q : (i : ι) × Tweak × prob.thColl.Msg i)
    (hnew : ¬ TweakReserved id qsChal q.2.1) :
    ((SM_DT_UD_oracles world prob pk (.inr (.inr q))).run (qsChal, twsColl) >>= fun r =>
        (SM_DT_UD_oracles world prob pk (.inr (.inr q))).run r.2) =
      pure (some (prob.thColl.eval q.1 pk q.2.1 q.2.2),
        (qsChal, twsColl ++ [q.2.1, q.2.1])) := by
  simp [SM_DT_UD_oracles, collectionOracle, hnew]

end CollectionHalf

end TweakableHash
