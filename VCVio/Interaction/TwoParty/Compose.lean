/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Append
import VCVio.Interaction.Basic.Replicate
import VCVio.Interaction.TwoParty.Decoration
import VCVio.Interaction.TwoParty.Strategy
import Mathlib.Control.Monad.Basic
import ToMathlib.Control.Lawful.Basic
import Mathlib.Data.Sigma.Basic
import VCVio.Interaction.Basic.StateChain

/-!
# Composing two-party protocols

Role-aware composition of strategies and counterparts along `Spec.append`, `Spec.replicate`,
and `Spec.stateChain`. Each combinator dispatches on the role at each node (sending or receiving)
to compose the two-party strategies correctly.

For binary composition, `comp` and `Counterpart.append` use `Transcript.liftAppend`
for the output type (factored form). The flat variants (`compFlat`,
`Counterpart.appendFlat`) take a single output family on the combined transcript.
-/

open LawfulMonad

universe u v

namespace Interaction
namespace Spec
namespace TwoParty

variable {m : Type u → Type u}
open _root_.Interaction.TwoParty

/-- A lawful monad whose independent effects may be swapped.

This is the exact extra structure needed for the sequential-composition
execution theorems once both sides may perform effects after a sender move is
observed: the composed prover may prepare suffix state before the counterpart
finishes its sender-side observation, so proving the usual factorization law
requires commuting those independent effects. -/
class LawfulCommMonad (m : Type u → Type u) [Monad m] extends LawfulMonad m where
  bind_comm :
    {α β γ : Type u} →
    (ma : m α) →
    (mb : m β) →
    (k : α → β → m γ) →
    (do
      let a ← ma
      let b ← mb
      k a b) =
    (do
      let b ← mb
      let a ← ma
      k a b)

private theorem bind_pure_sigma_mk {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {α : Type u} {β : α → Type u} (x : α) {tail : β x} {action : m (β x)}
    (h : action = pure tail) :
    (do
      let rest ← action
      pure (Sigma.mk x rest)) = pure (Sigma.mk x tail) := by
  rw [h]
  simp [monad_norm]

/-- Compose role-aware strategies along `Spec.append` with a two-argument output family
lifted through `Transcript.liftAppend`. The continuation receives the first phase's
output and produces a second-phase strategy. -/
def Focal.comp {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {F : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁) (F tr₁))) :
    m (StrategyOver (pairedSyntax m) Participant.focal (s₁.append s₂) (r₁.append r₂)
      (Spec.Transcript.liftAppend s₁ s₂ F)) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let rest ← comp next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
        pure ⟨x, rest⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        comp next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Compose role-aware strategies along `Spec.append` with a single output family
on the combined transcript. The continuation indexes via `Transcript.append`. -/
def Focal.compFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))) :
    m (StrategyOver (pairedSyntax m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let rest ← compFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
        pure ⟨x, rest⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        compFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Pure continuation specialization of `compFlat`. This stays private:
it only serves the weaker `[LawfulMonad]` execution theorem below. -/
private def Focal.compFlatPure {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    StrategyOver (pairedSyntax m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ => do
      let ⟨x, next⟩ ← strat₁
      pure ⟨x, compFlatPure next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      fun x => do
        let next ← strat₁ x
        pure (compFlatPure next (fun tr₁ mid => f ⟨x, tr₁⟩ mid))

private theorem Focal.compFlat_eq_pure_compFlatPure
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid)) =
      pure (Focal.compFlatPure strat₁ f) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {Mid : Spec.Transcript s₁ → Type u}
      {Output : Spec.Transcript (s₁.append s₂) → Type u}
      (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ Mid)
      (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
        StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
      Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid)) =
        pure (Focal.compFlatPure strat₁ f) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        rfl
    | .node X rest, ⟨.sender, rRest⟩ =>
        rw [Focal.compFlat.eq_2]
        refine congrArg pure ?_
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        cases xc with
        | mk x next =>
            simp only [bind_pure_comp]
            have hgo := go (rest x) (rRest x)
              (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
              (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
              (Output := fun tr => Output ⟨x, tr⟩)
              next
              (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
            exact (congrArg (fun z => Sigma.mk x <$> z) hgo).trans (map_pure _ _)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        rw [Focal.compFlat.eq_3]
        refine congrArg pure ?_
        funext x
        refine congrArg (fun k => strat₁ x >>= k) ?_
        funext next
        exact go (rest x) (rRest x)
          (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
          (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
          (Output := fun tr => Output ⟨x, tr⟩)
          next
          (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
  exact go s₁ r₁ strat₁ f

/-- Extract the first-phase role-aware strategy from a strategy on a composed
interaction. At each first-phase transcript `tr₁`, the remainder is the
second-phase strategy with output indexed by `Transcript.append`. -/
def Focal.splitPrefix {m : Type u → Type u} [Functor m] :
    {s₁ : Spec} → {s₂ : Spec.Transcript s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)} →
    {Output : Spec.Transcript (s₁.append s₂) → Type u} →
    StrategyOver (pairedSyntax m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output →
    StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ (fun tr₁ =>
      StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
  | .done, _, _, _, _, strat => strat
  | .node _ _, s₂, ⟨.sender, rRest⟩, r₂, _, strat =>
      (fun ⟨x, cont⟩ =>
        ⟨x, splitPrefix
          (s₂ := fun p => s₂ ⟨x, p⟩)
          (r₁ := rRest x)
          (r₂ := fun p => r₂ ⟨x, p⟩) cont⟩) <$> strat
  | .node _ _, s₂, ⟨.receiver, rRest⟩, r₂, _, respond =>
      fun x => (splitPrefix
        (s₂ := fun p => s₂ ⟨x, p⟩)
        (r₁ := rRest x)
        (r₂ := fun p => r₂ ⟨x, p⟩) ·) <$> respond x

/-- Recompose a role-aware strategy from its prefix decomposition. -/
theorem Focal.compFlat_splitPrefix
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat : StrategyOver (pairedSyntax m) Participant.focal (s₁.append s₂) (r₁.append r₂) Output) :
    Focal.compFlat
      (Focal.splitPrefix (s₂ := s₂) (r₁ := r₁) (r₂ := r₂) strat)
      (fun _ strat₂ => pure strat₂) = pure strat := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {Output : Spec.Transcript (s₁.append s₂) → Type u}
      (strat : StrategyOver (pairedSyntax m) Participant.focal
        (s₁.append s₂) (r₁.append r₂) Output) :
      Focal.compFlat
        (Focal.splitPrefix (s₂ := s₂) (r₁ := r₁) (r₂ := r₂) strat)
        (fun _ strat₂ => pure strat₂) = pure strat := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        rfl
    | .node X rest, ⟨.sender, rRest⟩ =>
        rw [Focal.compFlat.eq_2, Focal.splitPrefix.eq_2]
        refine congrArg pure ?_
        simp only [bind_map_left]
        calc
          (do
            let a ← strat
            let rest_1 ←
              Focal.compFlat
                (Focal.splitPrefix
                  (s₂ := fun p => s₂ ⟨a.1, p⟩)
                  (r₁ := rRest a.1)
                  (r₂ := fun p => r₂ ⟨a.1, p⟩) a.2)
                (fun _ strat₂ => pure strat₂)
            pure ⟨a.1, rest_1⟩) =
              strat >>= fun a => pure ⟨a.1, a.2⟩ := by
                refine congrArg (fun k => strat >>= k) ?_
                funext xc
                rcases xc with ⟨x, tail⟩
                let Suffix : X → Type u := fun y =>
                  StrategyOver (pairedSyntax m) TwoParty.Participant.focal
                    ((fun b => PFunctor.FreeM.append (rest b) (fun path => s₂ ⟨b, path⟩)) y)
                    ((fun y => (rRest y).append fun p => r₂ ⟨y, p⟩) y)
                    (fun tr => Output ⟨y, tr⟩)
                have hgo :
                    (Focal.compFlat (Focal.splitPrefix tail)
                      (fun _ strat₂ => pure strat₂)) = pure tail :=
                  go (rest x) (rRest x)
                    (s₂ := fun p => s₂ ⟨x, p⟩)
                    (r₂ := fun p => r₂ ⟨x, p⟩) tail
                exact bind_pure_sigma_mk (m := m) (α := X) (β := Suffix)
                  (x := x) (tail := tail)
                  (action := Focal.compFlat (Focal.splitPrefix tail)
                    (fun _ strat₂ => pure strat₂)) hgo
          _ = strat := by
                simp
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        refine congrArg pure ?_
        funext x
        simp only [Focal.splitPrefix.eq_3]
        have hcont :
            strat x >>= (fun next =>
              Focal.compFlat
                (Focal.splitPrefix
                  (s₂ := fun p => s₂ ⟨x, p⟩)
                  (r₁ := rRest x)
                  (r₂ := fun p => r₂ ⟨x, p⟩) next)
                (fun _ strat₂ => pure strat₂)) =
              strat x >>= fun next => pure next := by
          refine congrArg (fun k => strat x >>= k) ?_
          funext next
          simpa using
            go (rest x) (rRest x)
              (s₂ := fun p => s₂ ⟨x, p⟩)
              (r₂ := fun p => r₂ ⟨x, p⟩) next
        simpa [monad_norm] using hcont
  exact go s₁ r₁ strat

/-- Compose counterparts along `Spec.append` with a two-argument output family
lifted through `Transcript.liftAppend`. The continuation maps the first phase's
output to a second-phase counterpart. -/
def Counterpart.append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : Spec.Transcript s₁ → Type u}
    {F : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u} :
    StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    StrategyOver (pairedSyntax m) Participant.counterpart (s₁.append s₂) (r₁.append r₂)
      (Spec.Transcript.liftAppend s₁ s₂ F) :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => do
        let cRest ← c₁ x
        pure <| Counterpart.append cRest (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.append cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- Compose counterparts along `Spec.append` with a single output family on the
combined transcript. The continuation indexes via `Transcript.append`. -/
def Counterpart.appendFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output₁ : Spec.Transcript s₁ → Type u}
    {Output₂ : Spec.Transcript (s₁.append s₂) → Type u} :
    StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output₂ (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) →
    StrategyOver (pairedSyntax m) Participant.counterpart (s₁.append s₂) (r₁.append r₂) Output₂ :=
  match s₁, r₁ with
  | .done, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩ => fun c₁ c₂ =>
      fun x => do
        let cRest ← c₁ x
        pure <| Counterpart.appendFlat cRest (fun p o => c₂ ⟨x, p⟩ o)
  | .node _ _, ⟨.receiver, _⟩ => fun c₁ c₂ => do
      let ⟨x, cRest⟩ ← c₁
      return ⟨x, Counterpart.appendFlat cRest (fun p o => c₂ ⟨x, p⟩ o)⟩

/-- `Counterpart.append` equals `appendFlat` composed with `mapOutput packAppend`.
This lets proofs that decompose an arbitrary strategy via `splitPrefix` +
`appendFlat` still work when `Reduction.comp` uses the non-flat `append`. -/
theorem Counterpart.append_eq_appendFlat_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m] :
    {s₁ : Spec} → {s₂ : Transcript s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)} →
    {Output₁ : Transcript s₁ → Type u} →
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u} →
    (c₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ Output₁) →
    (c₂ : (tr₁ : Transcript s₁) → Output₁ tr₁ →
      StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    Counterpart.append c₁ c₂ =
      Counterpart.appendFlat c₁ (fun tr₁ o =>
        Counterpart.mapOutput
          (fun tr₂ x => Transcript.packAppend s₁ s₂ F tr₁ tr₂ x) (c₂ tr₁ o))
  | .done, _, _, _, _, _, c₁, c₂ => by
      simp only [Counterpart.append, Counterpart.appendFlat, Transcript.packAppend]
      exact (Counterpart.mapOutput_id _).symm
  | .node _ rest, _, ⟨.sender, rRest⟩, _, _, _, c₁, c₂ => by
      funext x
      refine congrArg (fun k => c₁ x >>= k) ?_
      funext cRest
      simpa [monad_norm] using
        congrArg pure
          (append_eq_appendFlat_mapOutput cRest (fun p o => c₂ ⟨x, p⟩ o))
  | .node _ rest, _, ⟨.receiver, rRest⟩, _, _, _, c₁, c₂ => by
      simp only [Counterpart.append, Counterpart.appendFlat]
      congr 1; funext ⟨x, cRest⟩; congr 1
      simp only [Transcript.packAppend]; congr 1
      exact append_eq_appendFlat_mapOutput cRest (fun p o => c₂ ⟨x, p⟩ o)

/-- Executing a flat composed strategy/counterpart factors into first executing
the prefix interaction and then executing the suffix continuation. -/
theorem run_compFlat_appendFlat_pure
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : Spec.Transcript s₁ → Type u}
    {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ MidP)
    (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
      StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
    (cpt₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ MidC)
    (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
      StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    (do
      let strat ← Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid))
      run (s₁.append s₂) (r₁.append r₂) strat
        (Counterpart.appendFlat cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← run s₁ r₁ strat₁ cpt₁
        let ⟨tr₂, outP, outC⟩ ←
          run (s₂ tr₁) (r₂ tr₁) (f tr₁ mid) (cpt₂ tr₁ out₁)
        pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : Spec.Transcript s₁ → Type u}
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
      {β : Type u}
      (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ MidP)
      (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
        StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
      (cpt₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ MidC)
      (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
        StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
      (g : ((tr : Spec.Transcript (s₁.append s₂)) × OutputP tr × OutputC tr) → m β) :
      (do
        let r ←
          do let strat ← Focal.compFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid))
             run (s₁.append s₂) (r₁.append r₂) strat
               (Counterpart.appendFlat cpt₁ cpt₂)
        g r) =
        (do
          let r₁ ← run s₁ r₁ strat₁ cpt₁
          let r₂ ←
            run (s₂ r₁.1) (r₂ r₁.1) (f r₁.1 r₁.2.1) (cpt₂ r₁.1 r₁.2.2)
          g ⟨Spec.Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2.1, r₂.2.2⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [Focal.compFlat.eq_1, Counterpart.appendFlat.eq_1,
          run_done, Spec.append, Spec.Decoration.append, Spec.Transcript.append]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [Focal.compFlat.eq_2, Counterpart.appendFlat.eq_2]
        simp only [monad_norm, Spec.append, PFunctor.FreeM.append, Spec.Decoration.append,
          run_sender]
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        have hpure := @Focal.compFlat_eq_pure_compFlatPure m _ _
          (rest xc.fst) (fun p => s₂ ⟨xc.fst, p⟩) (rRest xc.fst) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => OutputP ⟨xc.fst, tr⟩)
          xc.snd
          (fun tr₁ mid =>
            show StrategyOver (pairedSyntax m) Participant.focal
                (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (fun tr₂ => OutputP ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun p => s₂ ⟨xc.fst, p⟩) tr₁ tr₂⟩)
            from f ⟨xc.fst, tr₁⟩ mid)
        erw [hpure, pure_bind]
        refine congrArg (fun k => cpt₁ xc.1 >>= k) ?_
        funext cRest
        have ih := @go (rest xc.fst) (rRest xc.fst)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => MidC ⟨xc.fst, tr⟩)
          (fun p => s₂ ⟨xc.fst, p⟩) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr => OutputP ⟨xc.fst, tr⟩) (fun tr => OutputC ⟨xc.fst, tr⟩)
          β xc.snd
          (fun tr₁ mid =>
            show StrategyOver (pairedSyntax m) Participant.focal
                (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (fun tr₂ => OutputP ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun p => s₂ ⟨xc.fst, p⟩) tr₁ tr₂⟩)
            from f ⟨xc.fst, tr₁⟩ mid)
          cRest
          (fun p o =>
            show StrategyOver (pairedSyntax m) Participant.counterpart
                (s₂ ⟨xc.fst, p⟩) (r₂ ⟨xc.fst, p⟩)
              (fun tr₂ => OutputC ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun q => s₂ ⟨xc.fst, q⟩) p tr₂⟩)
            from cpt₂ ⟨xc.fst, p⟩ o)
          (fun r => g ⟨⟨xc.fst, r.1⟩, r.2.1, r.2.2⟩)
        simp only [Focal.compFlat_eq_pure_compFlatPure, pure_bind] at ih
        exact ih
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [Focal.compFlat.eq_3, Counterpart.appendFlat.eq_3]
        simp only [monad_norm, Spec.append, PFunctor.FreeM.append, Spec.Decoration.append,
          run_receiver]
        refine congrArg (fun k => cpt₁ >>= k) ?_
        funext xc
        refine congrArg (fun k => strat₁ xc.1 >>= k) ?_
        funext next
        exact @go (rest xc.fst) (rRest xc.fst)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => MidC ⟨xc.fst, tr⟩)
          (fun p => s₂ ⟨xc.fst, p⟩) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr => OutputP ⟨xc.fst, tr⟩) (fun tr => OutputC ⟨xc.fst, tr⟩)
          β next
          (fun tr₁ mid =>
            show StrategyOver (pairedSyntax m) Participant.focal
                (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (fun tr₂ => OutputP ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun p => s₂ ⟨xc.fst, p⟩) tr₁ tr₂⟩)
            from f ⟨xc.fst, tr₁⟩ mid)
          xc.snd
          (fun p o =>
            show StrategyOver (pairedSyntax m) Participant.counterpart
                (s₂ ⟨xc.fst, p⟩) (r₂ ⟨xc.fst, p⟩)
              (fun tr₂ => OutputC ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun q => s₂ ⟨xc.fst, q⟩) p tr₂⟩)
            from cpt₂ ⟨xc.fst, p⟩ o)
          (fun r => g ⟨⟨xc.fst, r.1⟩, r.2.1, r.2.2⟩)
  simpa [monad_norm] using go s₁ r₁ strat₁ f cpt₁ cpt₂ pure

/-- Executing a flat composed strategy/counterpart factors into first executing
the prefix interaction and then executing the suffix continuation. -/
theorem run_compFlat_appendFlat
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : Spec.Transcript s₁ → Type u}
    {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ MidP)
    (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
      m (StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂))))
    (cpt₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ MidC)
    (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
      StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    (do
      let strat ← Focal.compFlat strat₁ f
      run (s₁.append s₂) (r₁.append r₂) strat
        (Counterpart.appendFlat cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← run s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC⟩ ←
          run (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
        pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : Spec.Transcript s₁ → Type u}
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
      {β : Type u}
      (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ MidP)
      (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
        m (StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂))))
      (cpt₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ MidC)
      (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
        StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
      (g : ((tr : Spec.Transcript (s₁.append s₂)) × OutputP tr × OutputC tr) → m β) :
      (do
        let r ←
          do let strat ← Focal.compFlat strat₁ f
             run (s₁.append s₂) (r₁.append r₂) strat
               (Counterpart.appendFlat cpt₁ cpt₂)
        g r) =
        (do
          let r₁ ← run s₁ r₁ strat₁ cpt₁
          let strat₂ ← f r₁.1 r₁.2.1
          let r₂ ←
            run (s₂ r₁.1) (r₂ r₁.1) strat₂ (cpt₂ r₁.1 r₁.2.2)
          g ⟨Spec.Transcript.append s₁ s₂ r₁.1 r₂.1, r₂.2.1, r₂.2.2⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [Focal.compFlat.eq_1, Counterpart.appendFlat.eq_1,
          run_done, Spec.append, Spec.Decoration.append, Spec.Transcript.append]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [Focal.compFlat.eq_2, Counterpart.appendFlat.eq_2]
        simp only [monad_norm, Spec.append, PFunctor.FreeM.append, Spec.Decoration.append,
          run_sender]
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        rw [LawfulCommMonad.bind_comm]
        refine congrArg (fun k => cpt₁ xc.1 >>= k) ?_
        funext cRest
        exact @go (rest xc.fst) (rRest xc.fst)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => MidC ⟨xc.fst, tr⟩)
          (fun p => s₂ ⟨xc.fst, p⟩) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr => OutputP ⟨xc.fst, tr⟩) (fun tr => OutputC ⟨xc.fst, tr⟩)
          β xc.snd
          (fun tr₁ mid =>
            show m (StrategyOver (pairedSyntax m) Participant.focal
              (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (fun tr₂ => OutputP ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun p => s₂ ⟨xc.fst, p⟩) tr₁ tr₂⟩))
            from f ⟨xc.fst, tr₁⟩ mid)
          cRest
          (fun p o =>
            show StrategyOver (pairedSyntax m) Participant.counterpart
                (s₂ ⟨xc.fst, p⟩) (r₂ ⟨xc.fst, p⟩)
              (fun tr₂ => OutputC ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun q => s₂ ⟨xc.fst, q⟩) p tr₂⟩)
            from cpt₂ ⟨xc.fst, p⟩ o)
          (fun r => g ⟨⟨xc.fst, r.1⟩, r.2.1, r.2.2⟩)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [Focal.compFlat.eq_3, Counterpart.appendFlat.eq_3]
        simp only [monad_norm, Spec.append, PFunctor.FreeM.append, Spec.Decoration.append,
          run_receiver]
        refine congrArg (fun k => cpt₁ >>= k) ?_
        funext xc
        refine congrArg (fun k => strat₁ xc.1 >>= k) ?_
        funext next
        exact @go (rest xc.fst) (rRest xc.fst)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => MidC ⟨xc.fst, tr⟩)
          (fun p => s₂ ⟨xc.fst, p⟩) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr => OutputP ⟨xc.fst, tr⟩) (fun tr => OutputC ⟨xc.fst, tr⟩)
          β next
          (fun tr₁ mid =>
            show m (StrategyOver (pairedSyntax m) Participant.focal
              (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (fun tr₂ => OutputP ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun p => s₂ ⟨xc.fst, p⟩) tr₁ tr₂⟩))
            from f ⟨xc.fst, tr₁⟩ mid)
          xc.snd
          (fun p o =>
            show StrategyOver (pairedSyntax m) Participant.counterpart
                (s₂ ⟨xc.fst, p⟩) (r₂ ⟨xc.fst, p⟩)
              (fun tr₂ => OutputC ⟨xc.fst,
                Spec.Transcript.append (rest xc.fst) (fun q => s₂ ⟨xc.fst, q⟩) p tr₂⟩)
            from cpt₂ ⟨xc.fst, p⟩ o)
          (fun r => g ⟨⟨xc.fst, r.1⟩, r.2.1, r.2.2⟩)
  simpa [monad_norm] using go s₁ r₁ strat₁ f cpt₁ cpt₂ pure

/-- Executing a factored composed strategy/counterpart (using `comp` and
`Counterpart.append`) factors into first executing the prefix interaction and then
executing the suffix continuation. Outputs are transported via `packAppend`. -/
theorem run_comp_append
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : Spec.Transcript s₁ → Type u}
    {FP FC : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
    (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ MidP)
    (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
      m (StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁) (FP tr₁)))
    (cpt₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ MidC)
    (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
      StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (FC tr₁)) :
    (do
      let strat ← Focal.comp strat₁ f
      run (s₁.append s₂) (r₁.append r₂) strat
        (Counterpart.append cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← run s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC⟩ ←
          run (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
        pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂,
          Spec.Transcript.packAppend s₁ s₂ FP tr₁ tr₂ outP,
          Spec.Transcript.packAppend s₁ s₂ FC tr₁ tr₂ outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : Spec.Transcript s₁ → Type u}
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {FP FC : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
      {β : Type u}
      (strat₁ : StrategyOver (pairedSyntax m) Participant.focal s₁ r₁ MidP)
      (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
        m (StrategyOver (pairedSyntax m) Participant.focal (s₂ tr₁) (r₂ tr₁) (FP tr₁)))
      (cpt₁ : StrategyOver (pairedSyntax m) Participant.counterpart s₁ r₁ MidC)
      (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
        StrategyOver (pairedSyntax m) Participant.counterpart (s₂ tr₁) (r₂ tr₁) (FC tr₁))
      (g : ((tr : Spec.Transcript (s₁.append s₂)) ×
        Spec.Transcript.liftAppend s₁ s₂ FP tr ×
        Spec.Transcript.liftAppend s₁ s₂ FC tr) → m β) :
      (do
        let r ←
          do let strat ← Focal.comp strat₁ f
             run (s₁.append s₂) (r₁.append r₂) strat
               (Counterpart.append cpt₁ cpt₂)
        g r) =
        (do
          let r₁ ← run s₁ r₁ strat₁ cpt₁
          let strat₂ ← f r₁.1 r₁.2.1
          let r₂ ←
            run (s₂ r₁.1) (r₂ r₁.1) strat₂ (cpt₂ r₁.1 r₁.2.2)
          g ⟨Spec.Transcript.append s₁ s₂ r₁.1 r₂.1,
            Spec.Transcript.packAppend s₁ s₂ FP r₁.1 r₂.1 r₂.2.1,
            Spec.Transcript.packAppend s₁ s₂ FC r₁.1 r₂.1 r₂.2.2⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [Focal.comp, Counterpart.append,
          run_done, Spec.append, Spec.Decoration.append,
          Spec.Transcript.append, Spec.Transcript.liftAppend, Spec.Transcript.packAppend]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [Focal.comp, Counterpart.append]
        simp only [monad_norm, Spec.append, PFunctor.FreeM.append, Spec.Decoration.append,
          run_sender]
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        rw [LawfulCommMonad.bind_comm]
        refine congrArg (fun k => cpt₁ xc.1 >>= k) ?_
        funext cRest
        exact @go (rest xc.fst) (rRest xc.fst)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => MidC ⟨xc.fst, tr⟩)
          (fun p => s₂ ⟨xc.fst, p⟩) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr₁ tr₂ => FP ⟨xc.fst, tr₁⟩ tr₂)
          (fun tr₁ tr₂ => FC ⟨xc.fst, tr₁⟩ tr₂)
          β xc.snd
          (fun tr₁ mid =>
            show m (StrategyOver (pairedSyntax m) Participant.focal
              (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (FP ⟨xc.fst, tr₁⟩))
            from f ⟨xc.fst, tr₁⟩ mid)
          cRest
          (fun p o =>
            show StrategyOver (pairedSyntax m) Participant.counterpart
                (s₂ ⟨xc.fst, p⟩) (r₂ ⟨xc.fst, p⟩)
              (FC ⟨xc.fst, p⟩)
            from cpt₂ ⟨xc.fst, p⟩ o)
          (fun r => g ⟨⟨xc.fst, r.1⟩, r.2.1, r.2.2⟩)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [Focal.comp, Counterpart.append]
        simp only [monad_norm, Spec.append, PFunctor.FreeM.append, Spec.Decoration.append,
          run_receiver]
        refine congrArg (fun k => cpt₁ >>= k) ?_
        funext xc
        refine congrArg (fun k => strat₁ xc.1 >>= k) ?_
        funext next
        exact @go (rest xc.fst) (rRest xc.fst)
          (fun tr => MidP ⟨xc.fst, tr⟩) (fun tr => MidC ⟨xc.fst, tr⟩)
          (fun p => s₂ ⟨xc.fst, p⟩) (fun p => r₂ ⟨xc.fst, p⟩)
          (fun tr₁ tr₂ => FP ⟨xc.fst, tr₁⟩ tr₂)
          (fun tr₁ tr₂ => FC ⟨xc.fst, tr₁⟩ tr₂)
          β next
          (fun tr₁ mid =>
            show m (StrategyOver (pairedSyntax m) Participant.focal
              (s₂ ⟨xc.fst, tr₁⟩) (r₂ ⟨xc.fst, tr₁⟩)
              (FP ⟨xc.fst, tr₁⟩))
            from f ⟨xc.fst, tr₁⟩ mid)
          xc.snd
          (fun p o =>
            show StrategyOver (pairedSyntax m) Participant.counterpart
                (s₂ ⟨xc.fst, p⟩) (r₂ ⟨xc.fst, p⟩)
              (FC ⟨xc.fst, p⟩)
            from cpt₂ ⟨xc.fst, p⟩ o)
          (fun r => g ⟨⟨xc.fst, r.1⟩, r.2.1, r.2.2⟩)
  simpa [monad_norm] using go s₁ r₁ strat₁ f cpt₁ cpt₂ pure

/-- Role swapping commutes with replication. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    RoleDecoration.swap (roles.replicate n) = (RoleDecoration.swap roles).replicate n :=
  Spec.Decoration.map_replicate (fun _ => Role.swap) roles n

/-- `n`-fold counterpart iteration on `spec.replicate n`, threading state `β`
through each round. -/
def Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u} :
    (n : Nat) →
    (Fin n → β →
      StrategyOver (pairedSyntax m) Participant.counterpart spec roles (fun _ => β)) →
    β →
    StrategyOver (pairedSyntax m) Participant.counterpart
      (spec.replicate n) (roles.replicate n) (fun _ => β)
  | 0, _, b => b
  | n + 1, step, b =>
      Counterpart.appendFlat (step 0 b) (fun _ b' => iterate n (fun i => step i.succ) b')

/-- `n`-fold role-aware strategy iteration on `spec.replicate n`, threading state `α`
through each round. -/
def Focal.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α →
      m (StrategyOver (pairedSyntax m) Participant.focal spec roles (fun _ => α))) →
    α →
    m (StrategyOver (pairedSyntax m) Participant.focal
      (spec.replicate n) (roles.replicate n) (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    compFlat strat (fun _ mid => iterate n (fun i => step i.succ) mid)

/-- Compose counterparts along a state chain with stage-dependent output. At each stage,
the step transforms `Family i s` into a counterpart whose output is
`Family (i+1) (advance i s tr)`. The full state chain output is
`Transcript.stateChainFamily Family`. -/
def Counterpart.stateChainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      StrategyOver (pairedSyntax m) Participant.counterpart
        (spec i s) (roles i s) (fun tr => Family (i + 1) (advance i s tr))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    StrategyOver (pairedSyntax m) Participant.counterpart
      (Spec.stateChain Stage spec advance n i s)
      (Spec.Decoration.stateChain roles n i s) (Spec.Transcript.stateChainFamily Family n i s)
  | 0, _, _, b => b
  | n + 1, i, s, b =>
      Counterpart.append (step i s b)
        (fun tr b' => stateChainComp step n (i + 1) (advance i s tr) b')

/-- Compose role-aware strategies along a state chain with stage-dependent output.
At each stage, the step transforms `Family i s` into a strategy whose output is
`Family (i+1) (advance i s tr)`. The full state chain output is
`Transcript.stateChainFamily Family`. -/
def Focal.stateChainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (StrategyOver (pairedSyntax m) Participant.focal (spec i s) (roles i s)
        (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (StrategyOver (pairedSyntax m) Participant.focal (Spec.stateChain Stage spec advance n i s)
      (Spec.Decoration.stateChain roles n i s) (Spec.Transcript.stateChainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    comp strat
      (fun tr mid => stateChainComp step n (i + 1) (advance i s tr) mid)

end TwoParty
end Spec
end Interaction
