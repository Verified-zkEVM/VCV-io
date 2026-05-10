/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Replicate
import ToMathlib.PFunctor.Free.Displayed.StateChain

/-!
# State-indexed dependent chains (`Spec.stateChain`)

An `n`-stage state-indexed composition: at each stage `i`, the interaction is `spec i s`
where `s : Stage i` is the current state. After the stage completes with transcript `tr`,
the state advances to `advance i s tr : Stage (i + 1)`.

This file provides the spec-level state chain (`Spec.stateChain`), a transcript telescope type
(`Transcript.stateChain`), flattening operations (`Transcript.stateChainJoin` /
`stateChainUnjoin`), type-level lifting (`Transcript.stateChainLiftJoin`,
`PFunctor.FreeM.Path.stateChainFamily`), decorations, and strategy composition along state chains.

For the primary (stateless, continuation-style) chain API see `Spec.Chain` in
`VCVio.Interaction.Basic.Chain`.
-/

universe u v w

namespace Interaction
namespace Spec

/-- `n`-stage dependent composition: run `spec i s`, then advance to state
`advance i s tr` and repeat for `n` total stages. -/
abbrev stateChain (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → Spec :=
  PFunctor.FreeM.stateChain (P := Spec.basePFunctor) (α := PUnit.{u+1})
    PUnit.unit Stage spec advance

@[simp, grind =]
theorem stateChain_zero (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (i : Nat) (s : Stage i) :
    PFunctor.FreeM.stateChain PUnit.unit Stage spec advance 0 i s = Spec.done := rfl

theorem stateChain_succ (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (n : Nat) (i : Nat) (s : Stage i) :
    PFunctor.FreeM.stateChain PUnit.unit Stage spec advance (n + 1) i s =
      (spec i s).append
        (fun tr =>
          PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
            (advance i s tr)) :=
  rfl

/-- `replicate` is `stateChain` with trivial state `PUnit`. -/
theorem replicate_eq_stateChain (spec : Spec) (n : Nat) (i : Nat) :
    spec.replicate n = PFunctor.FreeM.stateChain PUnit.unit (fun _ => PUnit) (fun _ _ => spec)
      (fun _ _ _ => ⟨⟩) n i ⟨⟩ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [replicate_succ]
    congr 1; funext _; exact ih (i + 1)

/-- Decompose a `(n+1)`-stage state chain transcript into the first-stage transcript and
the remainder. Specialization of `PFunctor.FreeM.Path.split` to the state chain structure. -/
def Transcript.stateChainSplit
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i) :
    Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance (n + 1) i s) →
    (tr₁ : Transcript (spec i s)) ×
      Transcript
        (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
          (advance i s tr₁)) :=
  PFunctor.FreeM.Path.split (spec i s)
    (fun tr => PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1) (advance i s tr))

/-- Combine a first-stage transcript with a remainder state chain transcript into a
`(n+1)`-stage state chain transcript. Specialization of `PFunctor.FreeM.Path.append` to
state chains. -/
def Transcript.stateChainAppend
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript
      (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
        (advance i s tr₁))) :
    Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance (n + 1) i s) :=
  PFunctor.FreeM.Path.append (spec i s)
    (fun tr =>
      PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1) (advance i s tr))
    tr₁ tr₂

/-- Splitting after appending at the state chain level recovers the components. -/
@[simp, grind =]
theorem Transcript.stateChainSplit_stateChainAppend
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript
      (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
        (advance i s tr₁))) :
    Transcript.stateChainSplit n i s (Transcript.stateChainAppend n i s tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  PFunctor.FreeM.Path.split_append _ _ _ _

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
The n-ary analog of `PFunctor.FreeM.Path.append`, mirroring `List.join`. -/
def Transcript.stateChainJoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Transcript.stateChain Stage spec advance n i s →
    Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)
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
    Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s) →
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
    (tr : Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)) →
    Transcript.stateChainJoin Stage spec advance n i s
      (Transcript.stateChainUnjoin Stage spec advance n i s tr) = tr
  | 0, _, _, ⟨⟩ => rfl
  | n + 1, i, s, tr => by
      dsimp only [Transcript.stateChainUnjoin, Transcript.stateChainJoin]
      rw [stateChainJoin_unjoin n (i + 1)]
      exact PFunctor.FreeM.Path.append_split _ _ tr

/-- Lift a family indexed by the transcript telescope to a family on the combined
state chain transcript. Uses `PFunctor.FreeM.Path.liftAppend` at each stage, ensuring that
`stateChainLiftJoin ... F (stateChainJoin ... trs)` reduces **definitionally**
to `F trs`. -/
def Transcript.stateChainLiftJoin (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (Transcript.stateChain Stage spec advance n i s → Type u) →
    Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s) → Type u
  | 0, _, _, F, _ => F ⟨⟩
  | n + 1, i, s, F, tr =>
      PFunctor.FreeM.Path.liftAppend (spec i s)
        (fun tr₁ =>
          PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
            (advance i s tr₁))
        (fun tr₁ trRest =>
          Transcript.stateChainLiftJoin Stage spec advance n (i + 1) (advance i s tr₁)
            (fun rest => F ⟨tr₁, rest⟩) trRest)
        tr

variable {S : Type u → Type v} {L : Type u → Type v} {F : ∀ X, L X → Type w}

/-- Per-node labels along a state chain: at each stage, use `deco i s`. -/
abbrev Decoration.stateChain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (deco : (i : Nat) → (s : Stage i) → Decoration S (spec i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration S (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s) :=
  PFunctor.FreeM.Displayed.Decoration.stateChain
    (P := Spec.basePFunctor) (α := PUnit.{u+1}) (a := PUnit.unit)
    (advance := advance) deco

/-- Dependent decoration layer along a state chain, fibered over
`Decoration.stateChain`. -/
abbrev Decoration.Over.stateChain {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Over F (spec i s) (deco i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration.Over F (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)
      (Decoration.stateChain deco n i s) :=
  PFunctor.FreeM.Displayed.Decoration.Over.stateChain
    (P := Spec.basePFunctor) (α := PUnit.{u+1}) (a := PUnit.unit)
    (advance := advance) rDeco

/-- `Over.map` commutes with `Over.stateChain`. -/
theorem Decoration.Over.map_stateChain {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l)
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Over F (spec i s) (deco i s))
    (n : Nat) (i : Nat) (s : Stage i) :
    Decoration.Over.map η (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)
        (Decoration.stateChain deco n i s) (Decoration.Over.stateChain rDeco n i s) =
      Decoration.Over.stateChain (fun j t => Decoration.Over.map η (spec j t) (deco j t)
        (rDeco j t)) n i s :=
  PFunctor.FreeM.Displayed.Decoration.Over.map_stateChain
    (P := Spec.basePFunctor) (α := PUnit.{u+1}) η rDeco n i s

/-! ## State chain families -/

/-- The output type of state chain composition. Given a per-stage family `Family i s`,
this computes the type at the terminal stage by threading through `PFunctor.FreeM.Path.liftAppend`
at each step. Reduces **definitionally** when the transcript is built via
`PFunctor.FreeM.Path.append`, avoiding Nat-arithmetic casts.

This is the canonical output type for `Strategy.stateChainComp` and
`StrategyOver.TwoParty.Counterpart.stateChainComp`. -/
def PFunctor.FreeM.Path.stateChainFamily
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i stage) → Type u
  | 0, i, stage, _ => Family i stage
  | n + 1, i, stage, tr =>
      PFunctor.FreeM.Path.liftAppend (spec i stage)
        (fun tr₁ =>
          PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
            (advance i stage tr₁))
        (fun tr₁ trRest =>
          PFunctor.FreeM.Path.stateChainFamily Family n (i + 1) (advance i stage tr₁) trRest)
        tr

@[simp]
theorem PFunctor.FreeM.Path.stateChainFamily_zero
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u) (i : Nat) (s : Stage i) (tr : PUnit) :
    PFunctor.FreeM.Path.stateChainFamily (advance := advance) Family 0 i s tr = Family i s := rfl

/-- A constant family is unaffected by `stateChainFamily`. -/
theorem PFunctor.FreeM.Path.stateChainFamily_const
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (α : Type u) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    (tr : Transcript (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)) →
    PFunctor.FreeM.Path.stateChainFamily (advance := advance) (fun _ _ => α) n i s tr = α
  | 0, _, _, _ => rfl
  | n + 1, i, s, tr => by
      simp only [PFunctor.FreeM.Path.stateChainFamily]
      rw [PFunctor.FreeM.Path.liftAppend_congr (spec i s) _ _ _
        (fun tr₁ trR =>
          PFunctor.FreeM.Path.stateChainFamily_const α n (i + 1) (advance i s tr₁) trR)]
      exact PFunctor.FreeM.Path.liftAppend_const α (spec i s) _ tr

/-! ## Strategy composition along state chains -/

variable {m : Type u → Type u}

/-- Compose per-stage strategies along a state chain. At each stage, the step function
transforms `Family i s` into a strategy whose output is `Family (i+1) (advance i s tr)`.
The full state chain output is `PFunctor.FreeM.Path.stateChainFamily Family`. -/
def Strategy.stateChainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (Strategy.Plain m (spec i s) (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (Strategy.Plain m (PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)
      (PFunctor.FreeM.Path.stateChainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    Strategy.comp (spec i s)
      (fun tr => PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1) (advance i s tr))
      strat (fun tr mid => stateChainComp step n (i + 1) (advance i s tr) mid)

end Spec
end Interaction
