/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function, distinct-tweak, multi-target target-collision resistance with random sampling

The message space splits as a product `M × R`: the adversary supplies the message part, and the
challenge oracle draws the randomness part itself, resampling until the digest satisfies a predicate
`prop`. Winning means colliding with a recorded digest under the same tweak, at a `(message,
randomness)` pair different from the recorded one.

Shortened to `SM-rTCR` in the prose below; the declaration names keep the full label.

This is the notion behind a *randomized, failure-prone* encoding: the signer re-hashes a message
against fresh randomness until the encoding succeeds, and `prop` is the success test. It bounds the
probability that an adversary finds two messages with the same encoding.

## One phase, and where the hardness comes from

SM-TCR and SM-PRE withhold the public seed while the adversary selects targets, and remove the
challenge oracle once the seed is revealed. SM-rTCR does neither: the seed is an *input* to the
adversary, and the challenge oracle stays available through to its output. So the adversary is a
single field with no private state to carry between phases, and `unifSpec` is part of its oracle
bundle because there is no oracle-free second phase to hold its private randomness.

Hardness comes instead from the randomness `ρ` that the challenge oracle draws and reveals only in
its answer. Colliding with a recorded digest still requires hitting a value the adversary did not
choose.

## Resampling, and the two kinds of rejection

`SM_DT_RTCR_resample` is the paper's bounded loop, as structural recursion on the attempt budget:
draw `ρ`, evaluate, and answer as soon as the digest satisfies `prop`. At `numRetries = 0` it draws
nothing and answers `none`.

Both rejections a caller sees are `none`, and they differ in the history:

* at the target cap, or on a tweak already recorded, *nothing* is recorded;
* when resampling is exhausted, `(tweak, message, none)` *is* recorded, so the slot takes an index
  and consumes one of the `numTargets` targets.

The second is a formalization decision rather than a transcription: the paper inserts
`(T, M, ⊥)` and then indexes into a history holding that entry, without saying what `ρⱼ = ⊥` means
in the winning condition. `SM_DT_RTCR_IsCollision` gives an exhausted slot its own losing arm, since
there is no recorded pair to differ from and no recorded digest to collide with.

## Winning on the pair

The winning condition asks `(M*, ρ*) ≠ (Mⱼ, ρⱼ)`, not `M* ≠ Mⱼ`. Reusing the recorded message with
*fresh randomness* is a legitimate win, which is what separates this notion from SM-TCR, where the
challenge oracle draws nothing and the recorded message is the whole recorded input.

The paper writes the `j`-th history entry as `(Mⱼ, Tⱼ, ρⱼ)` where its own insertion step writes
`(T, M, ρ)`; the field order here follows the insertion step.

## No collection oracle

Every other game in this directory carries a `TweakableHashCollection` and a collection oracle, and
this one deliberately does not. The collection oracle exists because the stand-alone notions hand
the public parameters to the adversary only after all challenge queries are made, so it cannot
evaluate other members of the family itself. Definition 6 hands the seed over up front, so
`Th^λ(P, ·, ·)` would give the adversary nothing it cannot already compute. The parameter would be
provably inert.

The tweak discipline is still shared: `TweakReserved` is the same predicate the collection-carrying
games test against their challenge history, at `tweakOf := Prod.fst`.

## No final-validity form

There is no source-final-validity sibling of this module, because no source states one. Definition 6
is unambiguously rejection-on-arrival — its oracle returns `⊥` and leaves the history untouched —
and the framework that motivates the sticky-monitor presentation has no randomized-sampling notion
to present.

## Special cases

At `numRetries = 1` with `prop` constantly true this is multi-target extended target-collision
resistance with nonce, and it is also the hypothesis of the Winternitz encoding's target-collision
resistance. The target-sum Winternitz encoding needs both parameters non-trivial: `prop` tests
membership of the target-sum codeword set, and `numRetries` is the rejection-sampling budget.

## Query bounds

`numTargets` is the paper's `p`, the cap on challenge queries, and `numRetries` is its `K`, the
number of hash evaluations the challenge oracle may make per query. The paper's `q`, the number of
evaluations the *adversary* makes, is a quantity of the heuristic random-oracle analysis rather than
a parameter of the game; the bounds there are stated in `q' = q + pK`, which is why `K` has to be
visible in the game at all.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1 Def. 6, Lem. 6 and Lem. 8 for the
  encodings that consume it, Cor. 1 and Cor. 2 for the two parameter settings, and Supplementary
  Material C for the random-oracle bound.
- Grilo, Hövelmanns, Hülsing and Majenz, *Tight Adaptive Reprogramming in the QROM*,
  [ePrint 2020/1361](https://eprint.iacr.org/2020/1361), for the nM-eTCR special case.
- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 7, for the collection oracle this game
  deliberately omits.
-/

public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {PkSeed Tweak M R Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a `(tweak, message)` pair, and the response is
`Option (Y × R)` — the digest together with the randomness that produced it, or `none` for the
paper's `⊥`. -/
abbrev SM_DT_RTCR_challengeSpec (Tweak M R Y : Type) : OracleSpec (Tweak × M) :=
  (Tweak × M) →ₒ Option (Y × R)

/-- An SM-rTCR problem: a tweakable hash on the split message space `M × R`, the predicate the
digest must satisfy, the bound on the number of targets, and the bound on resampling attempts per
query. -/
structure SM_DT_RTCR_Problem (PkSeed Tweak M R Y : Type) where
  /-- The tweakable hash whose target-collision resistance under random sampling is in question. -/
  th : TweakableHash PkSeed Tweak (M × R) Y
  /-- The property of the digest that the challenge oracle resamples for. In an application this is
  the success test of a randomized encoding. -/
  prop : Y → Bool
  /-- The cap on accepted challenge-oracle queries. -/
  numTargets : ℕ
  /-- The cap on resampling attempts within a single query, and so on the hash evaluations the
  challenge oracle makes to answer one. -/
  numRetries : ℕ

/-- The state threaded through the SM-rTCR challenge oracle: the history of accepted targets, each
recording the queried tweak and message together with the randomness the oracle used, or `none`
where resampling was exhausted. -/
abbrev SM_DT_RTCR_State (Tweak M R : Type) : Type := List (Tweak × M × Option R)

/-- An SM-rTCR adversary: a single phase, taking the public seed as an input and keeping the
challenge oracle to the end, which names a target index together with a message and randomness
colliding with it.

There is no `State` field and no second phase. `unifSpec` is in the oracle bundle because this
phase is where the adversary's private randomness has to live. -/
structure SM_DT_RTCR_Adversary (prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y) where
  /-- Given the public seed, and with the challenge oracle available throughout, name a target index
  and a colliding `(message, randomness)` pair. -/
  main : PkSeed → OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y) (ℕ × M × R)

/-- The resampling loop: draw `ρ` from `R`, and answer with the digest paired with the `ρ` that
produced it as soon as that digest satisfies `prop`, giving up after `attempts` draws.

At `attempts = 0` this draws nothing and answers `none`, so the loop is total at every budget. -/
@[expose] noncomputable def SM_DT_RTCR_resample [SampleableType R]
    (prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y) (pk : PkSeed) (t : Tweak) (m : M) :
    ℕ → ProbComp (Option (Y × R))
  | 0 => pure none
  | attempts + 1 => do
      let ρ ← $ᵗ R
      let y := prob.th.eval pk t (m, ρ)
      if prob.prop y then pure (some (y, ρ))
      else SM_DT_RTCR_resample prob pk t m attempts

/-- The challenge oracle at a public seed. A query is rejected with `none`, and leaves the history
untouched, when the target cap is reached or when its tweak is already recorded. Otherwise the
oracle resamples and records a slot either way: the randomness it used on success, and `none` in its
place on exhaustion.

Recording the answer's randomness with `Option.map Prod.snd` is what makes an exhausted slot consume
a target by construction rather than by a separate branch.

Accepted queries are appended, so the history is in issue order and its `j`-th entry is the `j`-th
target. -/
@[expose] noncomputable def SM_DT_RTCR_challengeOracle [DecidableEq Tweak] [SampleableType R]
    (prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y) (pk : PkSeed) :
    QueryImpl (SM_DT_RTCR_challengeSpec Tweak M R Y)
      (StateT (SM_DT_RTCR_State Tweak M R) ProbComp) :=
  fun tm => do
    let qsChal ← get
    if prob.numTargets ≤ qsChal.length ∨ TweakReserved Prod.fst qsChal tm.1 then
      return none
    else
      let res ← ((SM_DT_RTCR_resample prob pk tm.1 tm.2 prob.numRetries :
        ProbComp (Option (Y × R))) : StateT (SM_DT_RTCR_State Tweak M R) ProbComp (Option (Y × R)))
      set (qsChal ++ [(tm.1, tm.2, res.map Prod.snd)])
      return res

/-- Both oracles available to the adversary over the challenge history, at a public seed: its own
uniform randomness, and the challenge oracle. -/
@[expose] noncomputable def SM_DT_RTCR_oracles [DecidableEq Tweak] [SampleableType R]
    (prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y) (pk : PkSeed) :
    QueryImpl (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y)
      (StateT (SM_DT_RTCR_State Tweak M R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM_DT_RTCR_State Tweak M R) ProbComp) +
    SM_DT_RTCR_challengeOracle prob pk

/-- The winning condition, on a challenge history and the adversary's output. There are three arms,
and only the third can win:

* an index outside the history loses;
* an index whose slot was recorded on exhausted resampling loses, since it holds no randomness to
  collide with and no digest was returned for it;
* otherwise the claim is a win exactly when the submitted pair differs from the recorded pair and
  the two agree under the recorded tweak.

Named rather than inlined into the experiment so that the arms can be pinned directly. -/
@[expose] def SM_DT_RTCR_IsCollision [DecidableEq M] [DecidableEq R] [DecidableEq Y]
    (prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y) (pk : PkSeed)
    (qsChal : SM_DT_RTCR_State Tweak M R) (out : ℕ × M × R) : Bool :=
  match qsChal[out.1]? with
  | none => false
  | some (_, _, none) => false
  | some (t, mj, some ρj) =>
      decide (out.2 ≠ (mj, ρj) ∧ prob.th.eval pk t out.2 = prob.th.eval pk t (mj, ρj))

/-- The SM-rTCR experiment. The public seed is sampled and handed to the adversary, which runs
against the challenge oracle throughout and wins under `SM_DT_RTCR_IsCollision`. -/
@[expose] noncomputable def SM_DT_RTCR_Experiment
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [SampleableType R] {prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y}
    (adv : SM_DT_RTCR_Adversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (out, qsChal) ← (simulateQ (SM_DT_RTCR_oracles prob pk) (adv.main pk)).run []
  return SM_DT_RTCR_IsCollision prob pk qsChal out

/-- The SM-rTCR advantage of an adversary. -/
@[expose] noncomputable def SM_DT_RTCR_Advantage
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [SampleableType R] {prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y}
    (adv : SM_DT_RTCR_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_RTCR_Experiment adv]

/-! ## The resampling loop -/

section Resample

variable [SampleableType R] {prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y} {pk : PkSeed}
  {t : Tweak} {m : M}

/-- At a zero attempt budget the loop draws nothing and gives up, so the challenge oracle is total
at `numRetries = 0` and answers every accepted query `none`. -/
theorem SM_DT_RTCR_resample_zero : SM_DT_RTCR_resample prob pk t m 0 = pure none := rfl

/-- With `prop` accepting everything, the first draw is answered, at every positive budget. -/
theorem SM_DT_RTCR_resample_of_prop_true (hprop : ∀ y, prob.prop y = true) (attempts : ℕ) :
    SM_DT_RTCR_resample prob pk t m (attempts + 1) =
      (fun ρ => some (prob.th.eval pk t (m, ρ), ρ)) <$> ($ᵗ R) := by
  simp [SM_DT_RTCR_resample, hprop]

/-- With `prop` rejecting everything, resampling is exhausted at every budget. -/
theorem SM_DT_RTCR_resample_eq_none_of_prop_false (hprop : ∀ y, prob.prop y = false)
    (attempts : ℕ) : ∀ z ∈ support (SM_DT_RTCR_resample prob pk t m attempts), z = none := by
  induction attempts with
  | zero => simp [SM_DT_RTCR_resample]
  | succ attempts ih => simpa [SM_DT_RTCR_resample, hprop] using ih

end Resample

/-! ## The challenge oracle's conventions -/

section ChallengeOracle

variable [DecidableEq Tweak] [SampleableType R] {prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y}
  {pk : PkSeed} {t : Tweak} {m : M} {qsChal : SM_DT_RTCR_State Tweak M R}

/-- A query at the target cap is rejected, the history is unchanged, and no randomness is drawn. -/
theorem SM_DT_RTCR_challengeOracle_run_of_full (hlen : prob.numTargets ≤ qsChal.length) :
    (SM_DT_RTCR_challengeOracle prob pk (t, m)).run qsChal = pure (none, qsChal) := by
  simp [SM_DT_RTCR_challengeOracle, hlen]

/-- A query reusing a tweak already in the history is rejected, the history is unchanged, and no
randomness is drawn. The reused tweak is rejected whatever message accompanies it, and whether or
not the slot holding it was exhausted. -/
theorem SM_DT_RTCR_challengeOracle_run_of_reused (m' : M) (ρ' : Option R)
    (hmem : (t, m', ρ') ∈ qsChal) :
    (SM_DT_RTCR_challengeOracle prob pk (t, m)).run qsChal = pure (none, qsChal) := by
  have hres : TweakReserved Prod.fst qsChal t := ⟨(t, m', ρ'), hmem, rfl⟩
  simp [SM_DT_RTCR_challengeOracle, hres]

/-- A query below the cap with a fresh tweak, when `prop` accepts everything and the retry budget is
positive, is answered on the first draw and records the randomness it used. -/
theorem SM_DT_RTCR_challengeOracle_run_of_fresh (hprop : ∀ y, prob.prop y = true)
    (hretries : prob.numRetries ≠ 0) (hlen : qsChal.length < prob.numTargets)
    (hnew : ¬ TweakReserved Prod.fst qsChal t) :
    (SM_DT_RTCR_challengeOracle prob pk (t, m)).run qsChal =
      (fun ρ => (some (prob.th.eval pk t (m, ρ), ρ),
        qsChal ++ [(t, m, some ρ)])) <$> ($ᵗ R) := by
  obtain ⟨attempts, hattempts⟩ := Nat.exists_eq_succ_of_ne_zero hretries
  simp [SM_DT_RTCR_challengeOracle, Nat.not_le.mpr hlen, hnew, hattempts, SM_DT_RTCR_resample,
    hprop, Functor.map_map]

/-- A query below the cap with a fresh tweak, when `prop` rejects everything, is answered `none` and
still records a slot, with `none` in place of the randomness.

This is the formalization decision the paper leaves open, so it is pinned rather than left to follow
from the definition: an exhausted query occupies an index and consumes one of the `numTargets`
targets, exactly as an answered one does. -/
theorem SM_DT_RTCR_challengeOracle_run_of_exhausted (hprop : ∀ y, prob.prop y = false)
    (hlen : qsChal.length < prob.numTargets) (hnew : ¬ TweakReserved Prod.fst qsChal t) :
    ∀ z ∈ support ((SM_DT_RTCR_challengeOracle prob pk (t, m)).run qsChal),
      z = (none, qsChal ++ [(t, m, none)]) := by
  intro z hz
  simp only [SM_DT_RTCR_challengeOracle, Nat.not_le.mpr hlen, hnew, or_self, ↓reduceIte,
    bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_map_left, support_bind, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨res, hres, hz⟩ := hz
  rw [SM_DT_RTCR_resample_eq_none_of_prop_false hprop _ res hres] at hz
  simpa using hz

end ChallengeOracle

/-! ## The winning condition's arms -/

section IsCollision

variable [DecidableEq M] [DecidableEq R] [DecidableEq Y]
  {prob : SM_DT_RTCR_Problem PkSeed Tweak M R Y} {pk : PkSeed}
  {qsChal : SM_DT_RTCR_State Tweak M R} {j : ℕ} {t : Tweak} {mj m : M} {ρj ρ : R}

/-- An index past the end of the challenge history loses. -/
theorem SM_DT_RTCR_isCollision_of_length_le (hj : qsChal.length ≤ j) :
    SM_DT_RTCR_IsCollision prob pk qsChal (j, m, ρ) = false := by
  simp [SM_DT_RTCR_IsCollision, List.getElem?_eq_none hj]

/-- A claim against a slot whose resampling was exhausted loses, whatever pair is submitted. That
slot holds no randomness, so there is no recorded input to collide with. -/
theorem SM_DT_RTCR_isCollision_of_exhausted (hj : qsChal[j]? = some (t, mj, none)) :
    SM_DT_RTCR_IsCollision prob pk qsChal (j, m, ρ) = false := by
  simp [SM_DT_RTCR_IsCollision, hj]

/-- Submitting the recorded pair back loses: the pair has to *differ* from the recorded one. -/
theorem SM_DT_RTCR_isCollision_of_replay (hj : qsChal[j]? = some (t, mj, some ρj)) :
    SM_DT_RTCR_IsCollision prob pk qsChal (j, mj, ρj) = false := by
  simp [SM_DT_RTCR_IsCollision, hj]

/-- Reusing the recorded *message* with different randomness wins, provided the digests agree. This
is what distinguishes Definition 6 from SM-TCR, whose winning condition asks the message to differ,
and it is the arm that would silently vanish if the condition were transcribed from there. -/
theorem SM_DT_RTCR_isCollision_of_same_message (hj : qsChal[j]? = some (t, mj, some ρj))
    (hρ : ρ ≠ ρj) (hcol : prob.th.eval pk t (mj, ρ) = prob.th.eval pk t (mj, ρj)) :
    SM_DT_RTCR_IsCollision prob pk qsChal (j, mj, ρ) = true := by
  simp [SM_DT_RTCR_IsCollision, hj, hcol, hρ]

end IsCollision

end TweakableHash
