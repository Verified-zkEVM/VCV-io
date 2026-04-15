/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.StateChain

/-!
# Continuation-style chains (`Spec.Chain`)

A `Chain n` is a self-contained recipe for an `n`-round protocol:
at each level it carries the current round's `Spec` and a transcript-indexed
continuation to the next level. There is **no external state type**, no
`Stage : Nat → Type`, and no round index family.

Converting to a `Spec` via `Chain.toSpec` uses only `Spec.append`.
State-machine constructions are *derived*: `Chain.ofStateMachine`
builds a chain from `(σ, step, next, s₀)` and then forgets `σ`.

## Main definitions

* `Spec.Chain` — depth-indexed telescope: round spec + continuation.
* `Spec.Chain.toSpec` — convert a chain into a concrete `Spec`.
* `Chain.replicate` — constant rounds (recovers `Spec.replicate`).
* `Chain.ofStateMachine` — build from a state machine (recovers `Spec.stateChain`).

## Three composition mechanisms

| Mechanism | State? | Transcript-dependent? | Use when |
|---|---|---|---|
| `Spec.replicate` | No | No | Uniform rounds (same spec, independent) |
| `Spec.stateChain` | Yes (`Stage i`) | Yes | State machine with explicit state type |
| `Spec.Chain` | No (baked in) | Yes | Continuation-style, no external state |

`Chain` is the most fundamental: it requires no external state type, yet
supports full transcript dependence. `stateChain` is a specialization
(recovered by `Chain.ofStateMachine`), and `replicate` is a further
specialization (recovered by `Chain.replicate`).

## Toy examples

The `GrowingMessages` section builds a protocol whose message type grows
at each step (`Fin 1`, `Fin 2`, …) without mentioning any state type.
-/

universe u

namespace Interaction
namespace Spec

/-- A self-contained recipe for an `n`-round protocol. At each level,
carries the current round's `Spec` and, for each possible transcript,
the recipe for the remaining rounds. No external state type. -/
def Chain : Nat → Type (u + 1)
  | 0 => PUnit
  | n + 1 => (spec : Spec) × (Transcript spec → Chain n)

namespace Chain

/-- Convert a chain into a concrete `Spec` via iterated `append`. -/
def toSpec : (n : Nat) → Chain n → Spec
  | 0, _ => .done
  | n + 1, ⟨spec, cont⟩ => spec.append (fun tr => toSpec n (cont tr))

@[simp, grind =]
theorem toSpec_zero (c : Chain 0) : toSpec 0 c = .done := rfl

theorem toSpec_succ {n : Nat} (spec : Spec)
    (cont : Transcript spec → Chain n) :
    toSpec (n + 1) ⟨spec, cont⟩ =
      spec.append (fun tr => toSpec n (cont tr)) := rfl

/-! ## Constructors -/

/-- Constant rounds: same spec every round, continuation ignores the
transcript. -/
def replicate (spec : Spec) : (n : Nat) → Chain n
  | 0 => ⟨⟩
  | n + 1 => ⟨spec, fun _ => replicate spec n⟩

/-- Build a chain from a state machine. The state `σ` is consumed
during construction and does not appear in the resulting `Chain`. -/
def ofStateMachine {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) : (n : Nat) → σ → Chain n
  | 0, _ => ⟨⟩
  | n + 1, s => ⟨step s, fun tr => ofStateMachine step next n (next s tr)⟩

/-! ## Bridge to existing API -/

/-- Converting a `replicate` chain recovers `Spec.replicate`. -/
theorem toSpec_replicate (spec : Spec) :
    (n : Nat) → toSpec n (Chain.replicate spec n) = spec.replicate n
  | 0 => rfl
  | n + 1 => by
      simp only [Chain.replicate, toSpec, Spec.replicate]
      congr 1; funext _; exact toSpec_replicate spec n

/-- Converting a state-machine chain recovers `Spec.stateChain` with
constant stage family and round index erased. -/
theorem toSpec_ofStateMachine {σ : Type u} (step : σ → Spec)
    (next : (s : σ) → Transcript (step s) → σ) :
    (n : Nat) → (i : Nat) → (s : σ) →
    toSpec n (Chain.ofStateMachine step next n s) =
      Spec.stateChain (fun _ => σ) (fun _ => step) (fun _ => next) n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [Chain.ofStateMachine, toSpec, Spec.stateChain]
      congr 1; funext tr
      exact toSpec_ofStateMachine step next n (i + 1) (next s tr)

/-! ## Transcript operations -/

/-- Split a transcript of an `(n+1)`-round chain into the first round's
transcript and the remainder. -/
def splitTranscript (n : Nat) (c : Chain (n + 1)) :
    Transcript (toSpec (n + 1) c) →
    (tr₁ : Transcript c.1) × Transcript (toSpec n (c.2 tr₁)) :=
  Transcript.split c.1 (fun tr => toSpec n (c.2 tr))

/-- Combine a first-round transcript with a remainder. -/
def appendTranscript (n : Nat) (c : Chain (n + 1))
    (tr₁ : Transcript c.1) (tr₂ : Transcript (toSpec n (c.2 tr₁))) :
    Transcript (toSpec (n + 1) c) :=
  Transcript.append c.1 (fun tr => toSpec n (c.2 tr)) tr₁ tr₂

@[simp, grind =]
theorem splitTranscript_appendTranscript (n : Nat) (c : Chain (n + 1))
    (tr₁ : Transcript c.1) (tr₂ : Transcript (toSpec n (c.2 tr₁))) :
    splitTranscript n c (appendTranscript n c tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_append _ _ _ _

/-! ## Strategy composition -/

/-- Output family for strategy composition along a chain. This is the intrinsic analog of
`Transcript.stateChainFamily`: a family on the remaining chain is lifted to a family on
transcripts of the flattened `Spec`. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type u) :
    (n : Nat) → (c : Chain n) → Transcript (toSpec n c) → Type u
  | 0, c, _ => Family c
  | n + 1, ⟨spec, cont⟩, tr =>
      Transcript.liftAppend spec (fun tr₁ => toSpec n (cont tr₁))
        (fun tr₁ tr₂ => outputFamily Family n (cont tr₁) tr₂)
        tr

/-- Compose strategies along a chain with a transcript-dependent output family. The step
function sees the current round spec packaged as the remaining chain, and returns the next
family member indexed by the transcript of that round. -/
def strategyComp {m : Type u → Type u} [Monad m]
    {Family : {n : Nat} → Chain n → Type u}
    (step : {n : Nat} → (c : Chain (n + 1)) → Family c →
      m (Strategy m c.1 (fun tr => Family (c.2 tr)))) :
    (n : Nat) → (c : Chain n) → Family c →
    m (Strategy m (toSpec n c) (outputFamily Family n c))
  | 0, _, a => pure a
  | n + 1, ⟨spec, cont⟩, a => do
      let strat ← step ⟨spec, cont⟩ a
      Strategy.comp spec (fun tr => toSpec n (cont tr))
        strat (fun tr mid => strategyComp step n (cont tr) mid)

end Chain

/-! ## Toy example: growing message types -/

section GrowingMessages

/-- A protocol where round `k` exchanges a value from `Fin (k + 1)`.
No state type — the dependency is baked directly into the chain. -/
private def growingChain : (n : Nat) → (k : Nat) → Chain.{0} n
  | 0, _ => ⟨⟩
  | n + 1, k => ⟨.node (Fin (k + 1)) fun _ => .done,
                  fun _ => growingChain n (k + 1)⟩

/-- Two rounds from position `0`: `Fin 1` then `Fin 2`. -/
example : Chain.toSpec 2 (growingChain 2 0) =
    .node (Fin 1) fun _ => .node (Fin 2) fun _ => .done := rfl

/-- Three rounds: `Fin 1`, `Fin 2`, `Fin 3`. -/
example : Chain.toSpec 3 (growingChain 3 0) =
    .node (Fin 1) fun _ => .node (Fin 2) fun _ =>
      .node (Fin 3) fun _ => .done := rfl

/-- The transcript type reflects the growing message sizes. -/
example : Transcript (Chain.toSpec 2 (growingChain 2 0)) =
    ((_ : Fin 1) × (_ : Fin 2) × PUnit) := rfl

/-- A fully literal 3-round protocol — no parameters, no recursion,
no state. Just data. -/
private def threeRoundsLiteral : Chain.{0} 3 :=
  ⟨.node (Fin 1) fun _ => .done, fun _ =>
    ⟨.node (Fin 2) fun _ => .done, fun _ =>
      ⟨.node (Fin 3) fun _ => .done, fun _ => ⟨⟩⟩⟩⟩

example : Chain.toSpec 3 threeRoundsLiteral =
    .node (Fin 1) fun _ => .node (Fin 2) fun _ =>
      .node (Fin 3) fun _ => .done := rfl

end GrowingMessages

/-! ## Toy example: genuine transcript-prefix dependence -/

section PrefixDependent

/-- First round branches and exposes branch-specific data to later rounds. -/
private def branchingRound : Spec :=
  .node Bool fun b =>
    if b then
      .node Nat fun _ => .done
    else
      .node (Fin 2) fun _ => .done

/-- The second round depends on the full first-round transcript. -/
private def secondRound : Transcript branchingRound → Spec
  | ⟨true, ⟨n, ⟨⟩⟩⟩ => .node (Fin (n + 1)) fun _ => .done
  | ⟨false, ⟨i, ⟨⟩⟩⟩ => .node (Fin (i.val + 2)) fun _ => .done

/-- The third round depends on the full two-round transcript prefix. -/
private def thirdRound :
    (tr₁ : Transcript branchingRound) → Transcript (secondRound tr₁) → Spec
  | ⟨true, ⟨n, ⟨⟩⟩⟩, ⟨k, ⟨⟩⟩ => .node (Fin (n + k.val + 1)) fun _ => .done
  | ⟨false, ⟨i, ⟨⟩⟩⟩, ⟨k, ⟨⟩⟩ => .node (Fin (i.val + k.val + 2)) fun _ => .done

/-- A three-round chain whose final move type genuinely depends on the prefix transcript. -/
private def prefixDependent : Chain.{0} 3 :=
  ⟨branchingRound, fun tr₁ =>
    ⟨secondRound tr₁, fun tr₂ =>
      ⟨thirdRound tr₁ tr₂, fun _ => ⟨⟩⟩⟩⟩

/-- Flattening the chain is just iterated `Spec.append` over transcript-indexed tails. -/
example : Chain.toSpec 3 prefixDependent =
    branchingRound.append (fun tr₁ =>
      (secondRound tr₁).append (fun tr₂ =>
        (thirdRound tr₁ tr₂).append (fun _ => .done))) := rfl

/-- After a `true` prefix, the remainder remembers the earlier `Nat` choice. -/
example (n : Nat) :
    Chain.toSpec 2 (prefixDependent.2 ⟨true, ⟨n, ⟨⟩⟩⟩) =
      .node (Fin (n + 1)) fun k =>
        .node (Fin (n + k.val + 1)) fun _ => .done := rfl

/-- After a `false` prefix, the remainder remembers the earlier `Fin 2` choice. -/
example (i : Fin 2) :
    Chain.toSpec 2 (prefixDependent.2 ⟨false, ⟨i, ⟨⟩⟩⟩) =
      .node (Fin (i.val + 2)) fun k =>
        .node (Fin (i.val + k.val + 2)) fun _ => .done := rfl

/-- The transcript type itself is dependent: the third move type varies with the second. -/
example (n : Nat) :
    Transcript (Chain.toSpec 2 (prefixDependent.2 ⟨true, ⟨n, ⟨⟩⟩⟩)) =
      ((k : Fin (n + 1)) × ((_ : Fin (n + k.val + 1)) × PUnit)) := rfl

/-- The other branch has a different dependent transcript shape. -/
example (i : Fin 2) :
    Transcript (Chain.toSpec 2 (prefixDependent.2 ⟨false, ⟨i, ⟨⟩⟩⟩)) =
      ((k : Fin (i.val + 2)) × ((_ : Fin (i.val + k.val + 2)) × PUnit)) := rfl

/-! ## Dependent strategy composition over the prefix-dependent example -/

/-- Pure strategy that follows a prescribed transcript and returns a chosen leaf output. -/
private def scriptStrategy :
    (spec : Spec) → (tr : Transcript spec) → {Output : Transcript spec → Type u} →
    Output tr → Strategy Id spec Output
  | .done, _, _, out => out
  | .node _ rest, ⟨x, trRest⟩, _, out => ⟨x, scriptStrategy (rest x) trRest out⟩

/-- Carry the flattened transcript of the remaining chain as the dependent state. -/
private abbrev ReplayState {n : Nat} (c : Chain.{0} n) : Type :=
  Transcript (Chain.toSpec n c)

/-- One dependent step: split the remaining flattened transcript into this round and the tail,
play the current round verbatim, and return the tail transcript. -/
private def replayStep {n : Nat} (c : Chain.{0} (n + 1))
    (tr : ReplayState c) :
    Id (Strategy Id c.1 (fun tr₁ => ReplayState (c.2 tr₁))) :=
  let ⟨tr₁, trRest⟩ := Chain.splitTranscript n c tr
  scriptStrategy c.1 tr₁ trRest

/-- Replay a full flattened transcript using the intrinsic dependent strategy combinator. -/
private def replayStrategy (n : Nat) (c : Chain.{0} n) (tr : ReplayState c) :
    Strategy Id (Chain.toSpec n c)
      (Chain.outputFamily (Family := fun {_} c => ReplayState c) n c) :=
  Chain.strategyComp (Family := fun {_} c => ReplayState c) replayStep n c tr

/-- A concrete `true`-branch transcript for the prefix-dependent chain. -/
private def trueReplayTranscript (n : Nat) (k : Fin (n + 1)) (j : Fin (n + k.val + 1)) :
    Transcript (Chain.toSpec 3 prefixDependent) := by
  let tr₁ : Transcript branchingRound := ⟨true, ⟨n, ⟨⟩⟩⟩
  let c₂ := prefixDependent.2 tr₁
  let tr₂ : Transcript c₂.1 := ⟨k, ⟨⟩⟩
  let c₃ := c₂.2 tr₂
  let tr₃ : Transcript c₃.1 := ⟨j, ⟨⟩⟩
  exact Chain.appendTranscript 2 prefixDependent tr₁
    (Chain.appendTranscript 1 c₂ tr₂
      (Chain.appendTranscript 0 c₃ tr₃ ⟨⟩))

/-- A concrete `false`-branch transcript for the prefix-dependent chain. -/
private def falseReplayTranscript (i : Fin 2) (k : Fin (i.val + 2))
    (j : Fin (i.val + k.val + 2)) :
    Transcript (Chain.toSpec 3 prefixDependent) := by
  let tr₁ : Transcript branchingRound := ⟨false, ⟨i, ⟨⟩⟩⟩
  let c₂ := prefixDependent.2 tr₁
  let tr₂ : Transcript c₂.1 := ⟨k, ⟨⟩⟩
  let c₃ := c₂.2 tr₂
  let tr₃ : Transcript c₃.1 := ⟨j, ⟨⟩⟩
  exact Chain.appendTranscript 2 prefixDependent tr₁
    (Chain.appendTranscript 1 c₂ tr₂
      (Chain.appendTranscript 0 c₃ tr₃ ⟨⟩))

/-- Replaying a concrete `true`-branch transcript reproduces that exact transcript. -/
example :
    (Strategy.run (spec := Chain.toSpec 3 prefixDependent)
      (replayStrategy 3 prefixDependent (trueReplayTranscript 1 0 0))).1 =
        trueReplayTranscript 1 0 0 := rfl

/-- Replaying a concrete `false`-branch transcript reproduces that exact transcript. -/
example :
    (Strategy.run (spec := Chain.toSpec 3 prefixDependent)
      (replayStrategy 3 prefixDependent (falseReplayTranscript 1 0 0))).1 =
        falseReplayTranscript 1 0 0 := rfl

end PrefixDependent

end Spec
end Interaction
