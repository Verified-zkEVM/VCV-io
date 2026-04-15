/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Replicate

/-!
# State-indexed dependent chains (`Spec.stateChain`)

An `n`-stage state-indexed composition: at each stage `i`, the interaction is `spec i s`
where `s : Stage i` is the current state. After the stage completes with transcript `tr`,
the state advances to `advance i s tr : Stage (i + 1)`.

This file provides the spec-level state chain (`Spec.stateChain`), a transcript telescope type
(`Transcript.stateChain`), flattening operations (`Transcript.stateChainJoin` /
`stateChainUnjoin`), type-level lifting (`Transcript.stateChainLiftJoin`,
`Transcript.stateChainFamily`), decorations, and strategy composition along state chains.

For the primary (stateless, continuation-style) chain API see `Spec.Chain` in
`VCVio.Interaction.Basic.Chain`.
-/

universe u v w

namespace Interaction
namespace Spec

/-- `n`-stage dependent composition: run `spec i s`, then advance to state
`advance i s tr` and repeat for `n` total stages. -/
def stateChain (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → Spec
  | 0, _, _ => .done
  | n + 1, i, s =>
      (spec i s).append (fun tr => stateChain Stage spec advance n (i + 1) (advance i s tr))

@[simp, grind =]
theorem stateChain_zero (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (i : Nat) (s : Stage i) :
    Spec.stateChain Stage spec advance 0 i s = .done := rfl

theorem stateChain_succ (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (n : Nat) (i : Nat) (s : Stage i) :
    Spec.stateChain Stage spec advance (n + 1) i s =
      (spec i s).append
        (fun tr => Spec.stateChain Stage spec advance n (i + 1) (advance i s tr)) :=
  rfl

/-- `replicate` is `stateChain` with trivial state `PUnit`. -/
theorem replicate_eq_stateChain (spec : Spec) (n : Nat) (i : Nat) :
    spec.replicate n = Spec.stateChain (fun _ => PUnit) (fun _ _ => spec)
      (fun _ _ _ => ⟨⟩) n i ⟨⟩ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [replicate, stateChain]
    congr 1; funext _; exact ih (i + 1)

/-- Decompose a `(n+1)`-stage state chain transcript into the first-stage transcript and
the remainder. Specialization of `Transcript.split` to the state chain structure. -/
def Transcript.stateChainSplit
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i) :
    Transcript (Spec.stateChain Stage spec advance (n + 1) i s) →
    (tr₁ : Transcript (spec i s)) ×
      Transcript (Spec.stateChain Stage spec advance n (i + 1) (advance i s tr₁)) :=
  Transcript.split (spec i s)
    (fun tr => Spec.stateChain Stage spec advance n (i + 1) (advance i s tr))

/-- Combine a first-stage transcript with a remainder state chain transcript into a
`(n+1)`-stage state chain transcript. Specialization of `Transcript.append` to
state chains. -/
def Transcript.stateChainAppend
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.stateChain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript (Spec.stateChain Stage spec advance (n + 1) i s) :=
  Transcript.append (spec i s)
    (fun tr => Spec.stateChain Stage spec advance n (i + 1) (advance i s tr)) tr₁ tr₂

/-- Splitting after appending at the state chain level recovers the components. -/
@[simp, grind =]
theorem Transcript.stateChainSplit_stateChainAppend
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.stateChain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript.stateChainSplit n i s (Transcript.stateChainAppend n i s tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_append _ _ _ _

/-! ## N-ary transcript operations -/

/-- Dependent telescope of per-stage transcripts: a sequence of individual-stage
transcripts where each stage determines the next via `advance`. Mirrors `Spec.stateChain`
at the transcript level. -/
def Transcript.stateChain (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Type u
  | 0, _, _ => PUnit
  | n + 1, i, s =>
      (tr : Transcript (spec i s)) ×
        Transcript.stateChain Stage spec advance n (i + 1) (advance i s tr)

/-- Flatten a transcript telescope into the combined state chain transcript,
concatenating each per-stage transcript via `Transcript.stateChainAppend`.
The n-ary analog of `Transcript.append`, mirroring `List.join`. -/
def Transcript.stateChainJoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Transcript.stateChain Stage spec advance n i s →
    Transcript (Spec.stateChain Stage spec advance n i s)
  | 0, _, _, _ => ⟨⟩
  | n + 1, i, s, ⟨tr₁, rest⟩ =>
      Transcript.stateChainAppend n i s tr₁
        (Transcript.stateChainJoin Stage spec advance n (i + 1) (advance i s tr₁) rest)

/-- Decompose a combined state chain transcript into a telescope of per-stage
transcripts. Inverse of `Transcript.stateChainJoin`. -/
def Transcript.stateChainUnjoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Transcript (Spec.stateChain Stage spec advance n i s) →
    Transcript.stateChain Stage spec advance n i s
  | 0, _, _, _ => ⟨⟩
  | n + 1, i, s, tr =>
      let ⟨tr₁, trRest⟩ := Transcript.stateChainSplit n i s tr
      ⟨tr₁, Transcript.stateChainUnjoin Stage spec advance n (i + 1) (advance i s tr₁) trRest⟩

/-- `stateChainUnjoin` after `stateChainJoin` is the identity on telescope transcripts. -/
@[simp]
theorem Transcript.stateChainUnjoin_join
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)} :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (trs : Transcript.stateChain Stage spec advance n i s) →
    Transcript.stateChainUnjoin Stage spec advance n i s
      (Transcript.stateChainJoin Stage spec advance n i s trs) = trs
  | 0, _, _, ⟨⟩ => rfl
  | n + 1, i, s, ⟨tr₁, rest⟩ => by
      dsimp only [Transcript.stateChainJoin, Transcript.stateChainUnjoin]
      rw [stateChainSplit_stateChainAppend]; dsimp only []
      rw [stateChainUnjoin_join]

/-- `stateChainJoin` after `stateChainUnjoin` is the identity on combined state chain
transcripts. -/
@[simp]
theorem Transcript.stateChainJoin_unjoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)} :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (tr : Transcript (Spec.stateChain Stage spec advance n i s)) →
    Transcript.stateChainJoin Stage spec advance n i s
      (Transcript.stateChainUnjoin Stage spec advance n i s tr) = tr
  | 0, _, _, ⟨⟩ => rfl
  | n + 1, i, s, tr => by
      dsimp only [Transcript.stateChainUnjoin, Transcript.stateChainJoin]
      rw [stateChainJoin_unjoin n (i + 1)]
      exact Transcript.append_split _ _ tr

/-- Lift a family indexed by the transcript telescope to a family on the combined
state chain transcript. Uses `Transcript.liftAppend` at each stage, ensuring that
`stateChainLiftJoin ... F (stateChainJoin ... trs)` reduces **definitionally**
to `F trs`. -/
def Transcript.stateChainLiftJoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (Transcript.stateChain Stage spec advance n i s → Type u) →
    Transcript (Spec.stateChain Stage spec advance n i s) → Type u
  | 0, _, _, F, _ => F ⟨⟩
  | n + 1, i, s, F, tr =>
      Transcript.liftAppend (spec i s)
        (fun tr₁ => Spec.stateChain Stage spec advance n (i + 1) (advance i s tr₁))
        (fun tr₁ trRest =>
          Transcript.stateChainLiftJoin Stage spec advance n (i + 1) (advance i s tr₁)
            (fun rest => F ⟨tr₁, rest⟩) trRest)
        tr

variable {S : Type u → Type v} {L : Type u → Type v} {F : ∀ X, L X → Type w}

/-- Per-node labels along a state chain: at each stage, use `deco i s`. -/
def Decoration.stateChain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (deco : (i : Nat) → (s : Stage i) → Decoration S (spec i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration S (Spec.stateChain Stage spec advance n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Decoration.append (deco i s)
        (fun tr => Decoration.stateChain deco n (i + 1) (advance i s tr))

/-- Dependent decoration layer along a state chain, fibered over
`Decoration.stateChain`. -/
def Decoration.Over.stateChain {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Over F (spec i s) (deco i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration.Over F (Spec.stateChain Stage spec advance n i s)
      (Decoration.stateChain deco n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Over.append (rDeco i s)
        (fun tr => Over.stateChain rDeco n (i + 1) (advance i s tr))

/-- `Over.map` commutes with `Over.stateChain`. -/
theorem Decoration.Over.map_stateChain {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l)
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Over F (spec i s) (deco i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration.Over.map η (Spec.stateChain Stage spec advance n i s)
        (Decoration.stateChain deco n i s) (Decoration.Over.stateChain rDeco n i s) =
      Decoration.Over.stateChain (fun j t => Decoration.Over.map η (spec j t) (deco j t)
        (rDeco j t)) n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [stateChain_succ, Decoration.stateChain, Decoration.Over.stateChain]
      rw [Decoration.Over.map_append η (spec i s)
            (fun tr => Spec.stateChain Stage spec advance n (i + 1) (advance i s tr))
            (deco i s)
            (fun tr => Decoration.stateChain deco n (i + 1) (advance i s tr))
            (rDeco i s)
            (fun tr => Decoration.Over.stateChain rDeco n (i + 1) (advance i s tr))]
      refine congrArg (Decoration.Over.append (Decoration.Over.map η (spec i s) (deco i s)
            (rDeco i s))) ?_
      funext tr
      exact Decoration.Over.map_stateChain η rDeco n (i + 1) (advance i s tr)

/-! ## State chain families -/

/-- The output type of state chain composition. Given a per-stage family `Family i s`,
this computes the type at the terminal stage by threading through `Transcript.liftAppend`
at each step. Reduces **definitionally** when the transcript is built via
`Transcript.append`, avoiding Nat-arithmetic casts.

This is the canonical output type for `Strategy.stateChainComp` and
`Counterpart.stateChainComp`. -/
def Transcript.stateChainFamily
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Transcript (Spec.stateChain Stage spec advance n i stage) → Type u
  | 0, i, stage, _ => Family i stage
  | n + 1, i, stage, tr =>
      Transcript.liftAppend (spec i stage)
        (fun tr₁ => Spec.stateChain Stage spec advance n (i + 1) (advance i stage tr₁))
        (fun tr₁ trRest =>
          Transcript.stateChainFamily Family n (i + 1) (advance i stage tr₁) trRest)
        tr

@[simp]
theorem Transcript.stateChainFamily_zero
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u) (i : Nat) (s : Stage i) (tr : PUnit) :
    Transcript.stateChainFamily (advance := advance) Family 0 i s tr = Family i s := rfl

/-- A constant family is unaffected by `stateChainFamily`. -/
theorem Transcript.stateChainFamily_const
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (α : Type u) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (tr : Transcript (Spec.stateChain Stage spec advance n i s)) →
    Transcript.stateChainFamily (advance := advance) (fun _ _ => α) n i s tr = α
  | 0, _, _, _ => rfl
  | n + 1, i, s, tr => by
      simp only [Transcript.stateChainFamily]
      rw [Transcript.liftAppend_congr (spec i s) _ _ _
        (fun tr₁ trR =>
          Transcript.stateChainFamily_const α n (i + 1) (advance i s tr₁) trR)]
      exact Transcript.liftAppend_const α (spec i s) _ tr

/-! ## Strategy composition along state chains -/

variable {m : Type u → Type u}

/-- Compose per-stage strategies along a state chain. At each stage, the step function
transforms `Family i s` into a strategy whose output is `Family (i+1) (advance i s tr)`.
The full state chain output is `Transcript.stateChainFamily Family`. -/
def Strategy.stateChainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (Strategy m (spec i s) (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (Strategy m (Spec.stateChain Stage spec advance n i s)
      (Transcript.stateChainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    Strategy.comp (spec i s)
      (fun tr => Spec.stateChain Stage spec advance n (i + 1) (advance i s tr))
      strat (fun tr mid => stateChainComp step n (i + 1) (advance i s tr) mid)

end Spec
end Interaction
