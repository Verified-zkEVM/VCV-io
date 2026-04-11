/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Append
import VCVio.Interaction.Basic.Replicate
import VCVio.Interaction.Basic.Chain
import VCVio.Interaction.TwoParty.Decoration
import VCVio.Interaction.TwoParty.Strategy
import Mathlib.Control.Monad.Basic

/-!
# Composing two-party protocols

Role-aware composition of strategies and counterparts along `Spec.append`, `Spec.replicate`,
and `Spec.stateChain`. Each combinator dispatches on the role at each node—sending or receiving—to
compose the two-party strategies correctly.

For binary composition, `compWithRoles` and `Counterpart.append` use `Transcript.liftAppend`
for the output type (factored form). The flat variants (`compWithRolesFlat`,
`Counterpart.appendFlat`) take a single output family on the combined transcript.
-/

universe u v

namespace Interaction
namespace Spec

variable {m : Type u → Type u}

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

/-- Compose role-aware strategies along `Spec.append` with a two-argument output family
lifted through `Transcript.liftAppend`. The continuation receives the first phase's
output and produces a second-phase strategy. -/
def Strategy.compWithRoles {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {F : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁) (F tr₁))) :
    m (Strategy.withRoles m (s₁.append s₂) (r₁.append r₂)
      (Spec.Transcript.liftAppend s₁ s₂ F)) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let rest ← compWithRoles next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
        pure ⟨x, rest⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        compWithRoles next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Compose role-aware strategies along `Spec.append` with a single output family
on the combined transcript. The continuation indexes via `Transcript.append`. -/
def Strategy.compWithRolesFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))) :
    m (Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output) :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let rest ← compWithRolesFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
        pure ⟨x, rest⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      pure fun x => do
        let next ← strat₁ x
        compWithRolesFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)

/-- Pure continuation specialization of `compWithRolesFlat`. This stays private:
it only serves the weaker `[LawfulMonad]` execution theorem below. -/
private def Strategy.compWithRolesFlatPure {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output :=
  match s₁, r₁ with
  | .done, _ => f ⟨⟩ strat₁
  | .node _ _, ⟨.sender, _⟩ => do
      let ⟨x, next⟩ ← strat₁
      pure ⟨x, compWithRolesFlatPure next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩
  | .node _ _, ⟨.receiver, _⟩ =>
      fun x => do
        let next ← strat₁ x
        pure (compWithRolesFlatPure next (fun tr₁ mid => f ⟨x, tr₁⟩ mid))

private theorem Strategy.compWithRolesFlat_eq_pure_compWithRolesFlatPure
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Spec.Transcript s₁ → Type u}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
      Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    Strategy.compWithRolesFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid)) =
      pure (Strategy.compWithRolesFlatPure strat₁ f) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {Mid : Spec.Transcript s₁ → Type u}
      {Output : Spec.Transcript (s₁.append s₂) → Type u}
      (strat₁ : Strategy.withRoles m s₁ r₁ Mid)
      (f : (tr₁ : Spec.Transcript s₁) → Mid tr₁ →
        Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
      Strategy.compWithRolesFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid)) =
        pure (Strategy.compWithRolesFlatPure strat₁ f) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        rfl
    | .node _ rest, ⟨.sender, rRest⟩ =>
        rw [Strategy.compWithRolesFlat.eq_2]
        refine congrArg pure ?_
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        cases xc with
        | mk x next =>
            simp only [bind_pure_comp]
            rw [go (rest x) (rRest x)
              (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
              (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
              (Output := fun tr => Output ⟨x, tr⟩)
              next
              (fun tr₁ mid => f ⟨x, tr₁⟩ mid)]
            simp
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        rw [Strategy.compWithRolesFlat.eq_3]
        refine congrArg pure ?_
        funext x
        refine congrArg (fun k => strat₁ x >>= k) ?_
        funext next
        rw [go (rest x) (rRest x)
          (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
          (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
          (Output := fun tr => Output ⟨x, tr⟩)
          next
          (fun tr₁ mid => f ⟨x, tr₁⟩ mid)]
  exact go s₁ r₁ strat₁ f

/-- Extract the first-phase role-aware strategy from a strategy on a composed
interaction. At each first-phase transcript `tr₁`, the remainder is the
second-phase strategy with output indexed by `Transcript.append`. -/
def Strategy.splitPrefixWithRoles {m : Type u → Type u} [Functor m] :
    {s₁ : Spec} → {s₂ : Spec.Transcript s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)} →
    {Output : Spec.Transcript (s₁.append s₂) → Type u} →
    Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output →
    Strategy.withRoles m s₁ r₁ (fun tr₁ =>
      Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
  | .done, _, _, _, _, strat => strat
  | .node _ _, s₂, ⟨.sender, rRest⟩, r₂, _, strat =>
      (fun ⟨x, cont⟩ =>
        ⟨x, splitPrefixWithRoles
          (s₂ := fun p => s₂ ⟨x, p⟩)
          (r₁ := rRest x)
          (r₂ := fun p => r₂ ⟨x, p⟩) cont⟩) <$> strat
  | .node _ _, s₂, ⟨.receiver, rRest⟩, r₂, _, respond =>
      fun x => (splitPrefixWithRoles
        (s₂ := fun p => s₂ ⟨x, p⟩)
        (r₁ := rRest x)
        (r₂ := fun p => r₂ ⟨x, p⟩) ·) <$> respond x

/-- Recompose a role-aware strategy from its prefix decomposition. -/
theorem Strategy.compWithRolesFlat_splitPrefixWithRoles
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Output : Spec.Transcript (s₁.append s₂) → Type u}
    (strat : Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output) :
    Strategy.compWithRolesFlat
      (Strategy.splitPrefixWithRoles (s₂ := s₂) (r₁ := r₁) (r₂ := r₂) strat)
      (fun _ strat₂ => pure strat₂) = pure strat := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {Output : Spec.Transcript (s₁.append s₂) → Type u}
      (strat : Strategy.withRoles m (s₁.append s₂) (r₁.append r₂) Output) :
      Strategy.compWithRolesFlat
        (Strategy.splitPrefixWithRoles (s₂ := s₂) (r₁ := r₁) (r₂ := r₂) strat)
        (fun _ strat₂ => pure strat₂) = pure strat := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        rfl
    | .node _ rest, ⟨.sender, rRest⟩ =>
        rw [Strategy.compWithRolesFlat.eq_2, Strategy.splitPrefixWithRoles.eq_2]
        refine congrArg pure ?_
        simp only [bind_map_left]
        calc
          (do
            let a ← strat
            let rest_1 ←
              Strategy.compWithRolesFlat
                (Strategy.splitPrefixWithRoles
                  (s₂ := fun p => s₂ ⟨a.1, p⟩)
                  (r₁ := rRest a.1)
                  (r₂ := fun p => r₂ ⟨a.1, p⟩) a.2)
                (fun _ strat₂ => pure strat₂)
            pure ⟨a.1, rest_1⟩) =
              strat >>= fun a => pure ⟨a.1, a.2⟩ := by
                refine congrArg (fun k => strat >>= k) ?_
                funext xc
                rw [go (rest xc.1) (rRest xc.1)
                  (s₂ := fun p => s₂ ⟨xc.1, p⟩)
                  (r₂ := fun p => r₂ ⟨xc.1, p⟩) xc.2]
                simp
          _ = strat := by
                simp
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        refine congrArg pure ?_
        funext x
        simp only [Strategy.splitPrefixWithRoles.eq_3]
        have hcont :
            strat x >>= (fun next =>
              Strategy.compWithRolesFlat
                (Strategy.splitPrefixWithRoles
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
        simpa [map_eq_bind_pure_comp, bind_assoc] using hcont
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
    Counterpart m s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    Counterpart m (s₁.append s₂) (r₁.append r₂)
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
    Counterpart m s₁ r₁ Output₁ →
    ((tr₁ : Spec.Transcript s₁) → Output₁ tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output₂ (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) →
    Counterpart m (s₁.append s₂) (r₁.append r₂) Output₂ :=
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
This lets proofs that decompose an arbitrary strategy via `splitPrefixWithRoles` +
`appendFlat` still work when `Reduction.comp` uses the non-flat `append`. -/
theorem Counterpart.append_eq_appendFlat_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m] :
    {s₁ : Spec} → {s₂ : Transcript s₁ → Spec} →
    {r₁ : RoleDecoration s₁} →
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)} →
    {Output₁ : Transcript s₁ → Type u} →
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u} →
    (c₁ : Counterpart m s₁ r₁ Output₁) →
    (c₂ : (tr₁ : Transcript s₁) → Output₁ tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁) (F tr₁)) →
    Counterpart.append c₁ c₂ =
      Counterpart.appendFlat c₁ (fun tr₁ o =>
        Counterpart.mapOutput
          (fun tr₂ x => Transcript.packAppend s₁ s₂ F tr₁ tr₂ x) (c₂ tr₁ o))
  | .done, _, _, _, _, _, c₁, c₂ => by
      simp [Counterpart.append, Counterpart.appendFlat,
        Transcript.packAppend, Counterpart.mapOutput_id]
  | .node _ rest, _, ⟨.sender, rRest⟩, _, _, _, c₁, c₂ => by
      funext x
      refine congrArg (fun k => c₁ x >>= k) ?_
      funext cRest
      simpa [bind_assoc] using
        congrArg pure
          (append_eq_appendFlat_mapOutput cRest (fun p o => c₂ ⟨x, p⟩ o))
  | .node _ rest, _, ⟨.receiver, rRest⟩, _, _, _, c₁, c₂ => by
      simp only [Counterpart.append, Counterpart.appendFlat]
      congr 1; funext ⟨x, cRest⟩; congr 1
      simp only [Transcript.packAppend]; congr 1
      exact append_eq_appendFlat_mapOutput cRest (fun p o => c₂ ⟨x, p⟩ o)

/-- Compose per-node-monad counterparts along `Spec.append` with a two-argument
output family lifted through `Transcript.liftAppend`. At each node, the recursive
composition is lifted through the node's `BundledMonad` via `Functor.map`. -/
def Counterpart.withMonads.append
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {md₁ : MonadDecoration s₁}
    {md₂ : (tr₁ : Transcript s₁) → MonadDecoration (s₂ tr₁)}
    {Output₁ : Transcript s₁ → Type u}
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u} :
    Counterpart.withMonads s₁ r₁ md₁ Output₁ →
    ((tr₁ : Transcript s₁) → Output₁ tr₁ →
      Counterpart.withMonads (s₂ tr₁) (r₂ tr₁) (md₂ tr₁) (F tr₁)) →
    Counterpart.withMonads (s₁.append s₂) (r₁.append r₂)
      (Decoration.append md₁ md₂) (Transcript.liftAppend s₁ s₂ F) :=
  match s₁, r₁, md₁ with
  | .done, _, _ => fun out₁ c₂ => c₂ ⟨⟩ out₁
  | .node _ _, ⟨.sender, _⟩, ⟨_, _⟩ => fun c₁ c₂ =>
      fun x => Functor.map
        (fun rec => append rec (fun p o => c₂ ⟨x, p⟩ o)) (c₁ x)
  | .node _ _, ⟨.receiver, _⟩, ⟨_, _⟩ => fun c₁ c₂ =>
      Functor.map
        (fun ⟨x, rec⟩ => ⟨x, append rec (fun p o => c₂ ⟨x, p⟩ o)⟩) c₁

/-- Executing a flat composed strategy/counterpart factors into first executing
the prefix interaction and then executing the suffix continuation. -/
theorem Strategy.runWithRoles_compWithRolesFlat_appendFlat_pure
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : Spec.Transcript s₁ → Type u}
    {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ MidP)
    (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
      Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
    (cpt₁ : Counterpart m s₁ r₁ MidC)
    (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    (do
      let strat ← Strategy.compWithRolesFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid))
      Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat
        (Counterpart.appendFlat cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles s₁ r₁ strat₁ cpt₁
        let ⟨tr₂, outP, outC⟩ ←
          Strategy.runWithRoles (s₂ tr₁) (r₂ tr₁) (f tr₁ mid) (cpt₂ tr₁ out₁)
        pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : Spec.Transcript s₁ → Type u}
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
      (strat₁ : Strategy.withRoles m s₁ r₁ MidP)
      (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
        Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂)))
      (cpt₁ : Counterpart m s₁ r₁ MidC)
      (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
        Counterpart m (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
      (do
        let strat ← Strategy.compWithRolesFlat strat₁ (fun tr₁ mid => pure (f tr₁ mid))
        Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat
          (Counterpart.appendFlat cpt₁ cpt₂)) =
        (do
          let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles s₁ r₁ strat₁ cpt₁
          let ⟨tr₂, outP, outC⟩ ←
            Strategy.runWithRoles (s₂ tr₁) (r₂ tr₁) (f tr₁ mid) (cpt₂ tr₁ out₁)
          pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [Strategy.compWithRolesFlat.eq_1, Counterpart.appendFlat.eq_1,
          Strategy.runWithRoles_done, Spec.append, Spec.Decoration.append, Spec.Transcript.append]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [append, Decoration.append, bind_pure_comp]
        rw [Strategy.compWithRolesFlat.eq_2, Counterpart.appendFlat.eq_2]
        simp only [Strategy.runWithRoles_sender, pure_bind, bind_assoc]
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        cases xc with
        | mk x next =>
            let addPrefix :
                ((tr : Spec.Transcript ((rest x).append (fun p => s₂ ⟨x, p⟩))) ×
                  (fun tr => OutputP ⟨x, tr⟩) tr × (fun tr => OutputC ⟨x, tr⟩) tr) →
                ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
              fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
            rw [Strategy.compWithRolesFlat_eq_pure_compWithRolesFlatPure
              (strat₁ := next)
              (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
              (r₁ := rRest x)
              (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
              (Output := fun tr => OutputP ⟨x, tr⟩)
              (f := fun tr₁ mid => f ⟨x, tr₁⟩ mid)]
            simp only [pure_bind]
            refine congrArg (fun k => cpt₁ x >>= k) ?_
            funext cNext
            let lhsBody :
                m
                  ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
                    OutputP tr × OutputC tr) := do
                  let strat₂ ←
                    Strategy.compWithRolesFlat next (fun tr₁ mid => pure (f ⟨x, tr₁⟩ mid))
                  addPrefix <$>
                    Strategy.runWithRoles
                      ((rest x).append fun p => s₂ ⟨x, p⟩)
                      ((rRest x).append fun p => r₂ ⟨x, p⟩)
                      strat₂
                      (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨x, p⟩ o))
            let midBody :
                m
                  ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
                    OutputP tr × OutputC tr) :=
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest x).append fun p => s₂ ⟨x, p⟩)
                  ((rRest x).append fun p => r₂ ⟨x, p⟩)
                  (Strategy.compWithRolesFlatPure next
                    (fun tr₁ mid => f ⟨x, tr₁⟩ mid))
                  (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨x, p⟩ o))
            let rhsBody :
                m
                  ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
                    OutputP tr × OutputC tr) := do
                  let ⟨tr₁, mid, out₁⟩ ←
                    Strategy.runWithRoles (rest x) (rRest x) next cNext
                  let ⟨tr₂, outP, outC⟩ ←
                    Strategy.runWithRoles
                      (s₂ ⟨x, tr₁⟩)
                      (r₂ ⟨x, tr₁⟩)
                      (f ⟨x, tr₁⟩ mid)
                      (cpt₂ ⟨x, tr₁⟩ out₁)
                  pure
                    ⟨⟨x, Spec.Transcript.append (rest x) (fun p => s₂ ⟨x, p⟩) tr₁ tr₂⟩,
                      outP, outC⟩
            have hPure : lhsBody = midBody := by
              simp [lhsBody, midBody, Strategy.compWithRolesFlat_eq_pure_compWithRolesFlatPure
                (strat₁ := next)
                (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
                (r₁ := rRest x)
                (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
                (Output := fun tr => OutputP ⟨x, tr⟩)
                (f := fun tr₁ mid => f ⟨x, tr₁⟩ mid)]
            have hGo : lhsBody = rhsBody := by
              simpa [lhsBody, rhsBody, Spec.Transcript.append, addPrefix] using
                congrArg (fun z => addPrefix <$> z)
                  (go (rest x) (rRest x)
                    (s₂ := fun tr₁ => s₂ ⟨x, tr₁⟩)
                    (r₂ := fun tr₁ => r₂ ⟨x, tr₁⟩)
                    (OutputP := fun tr => OutputP ⟨x, tr⟩)
                    (OutputC := fun tr => OutputC ⟨x, tr⟩)
                    next
                    (fun tr₁ mid => f ⟨x, tr₁⟩ mid)
                    cNext
                    (fun tr₁ out₁ => cpt₂ ⟨x, tr₁⟩ out₁))
            simpa [midBody, rhsBody] using hPure.symm.trans hGo
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [append, Decoration.append, bind_pure_comp]
        rw [Strategy.compWithRolesFlat.eq_3, Counterpart.appendFlat.eq_3]
        simp only [pure_bind]
        have hRunL := Strategy.runWithRoles_receiver
          (m := m)
          (X := _)
          (rest := fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))
          (rRest := fun x => (rRest x).append (fun p => r₂ ⟨x, p⟩))
          (OutputP := OutputP)
          (OutputC := OutputC)
          (fun x => do
            let next ← strat₁ x
            Strategy.compWithRolesFlat next (fun tr₁ mid => pure (f ⟨x, tr₁⟩ mid)))
          (do
            let ⟨x, next⟩ ← cpt₁
            pure ⟨x, Counterpart.appendFlat next (fun p o => cpt₂ ⟨x, p⟩ o)⟩)
        have hRunR := Strategy.runWithRoles_receiver
          (m := m)
          (X := _)
          (rest := rest)
          (rRest := rRest)
          (OutputP := MidP)
          (OutputC := MidC)
          strat₁ cpt₁
        rw [hRunL, hRunR]
        simp only [bind_assoc]
        refine congrArg (fun k => cpt₁ >>= k) ?_
        funext xc
        simp only [pure_bind]
        refine congrArg (fun k => strat₁ xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript ((rest xc.1).append (fun p => s₂ ⟨xc.1, p⟩))) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr × (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [Spec.Transcript.append, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1)
              (s₂ := fun tr₁ => s₂ ⟨xc.1, tr₁⟩)
              (r₂ := fun tr₁ => r₂ ⟨xc.1, tr₁⟩)
              (OutputP := fun tr => OutputP ⟨xc.1, tr⟩)
              (OutputC := fun tr => OutputC ⟨xc.1, tr⟩)
              next
              (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              xc.2
              (fun tr₁ out₁ => cpt₂ ⟨xc.1, tr₁⟩ out₁))
  exact go s₁ r₁ strat₁ f cpt₁ cpt₂

/-- Executing a flat composed strategy/counterpart factors into first executing
the prefix interaction and then executing the suffix continuation. -/
theorem Strategy.runWithRoles_compWithRolesFlat_appendFlat
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : Spec.Transcript s₁ → Type u}
    {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ MidP)
    (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂))))
    (cpt₁ : Counterpart m s₁ r₁ MidC)
    (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
    (do
      let strat ← Strategy.compWithRolesFlat strat₁ f
      Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat
        (Counterpart.appendFlat cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC⟩ ←
          Strategy.runWithRoles (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
        pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : Spec.Transcript s₁ → Type u}
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {OutputP OutputC : Spec.Transcript (s₁.append s₂) → Type u}
      (strat₁ : Strategy.withRoles m s₁ r₁ MidP)
      (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
        m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append s₁ s₂ tr₁ tr₂))))
      (cpt₁ : Counterpart m s₁ r₁ MidC)
      (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
        Counterpart m (s₂ tr₁) (r₂ tr₁)
          (fun tr₂ => OutputC (Spec.Transcript.append s₁ s₂ tr₁ tr₂))) :
      (do
        let strat ← Strategy.compWithRolesFlat strat₁ f
        Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat
          (Counterpart.appendFlat cpt₁ cpt₂)) =
        (do
          let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles s₁ r₁ strat₁ cpt₁
          let strat₂ ← f tr₁ mid
          let ⟨tr₂, outP, outC⟩ ←
            Strategy.runWithRoles (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
          pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂, outP, outC⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [Strategy.compWithRolesFlat.eq_1, Counterpart.appendFlat.eq_1,
          Strategy.runWithRoles_done, Spec.append, Spec.Decoration.append, Spec.Transcript.append]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [append, Decoration.append, bind_pure_comp]
        rw [Strategy.compWithRolesFlat.eq_2, Counterpart.appendFlat.eq_2]
        simp only [Strategy.runWithRoles_sender, pure_bind, bind_assoc]
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        let addPrefix :
            ((tr : Spec.Transcript ((rest xc.1).append (fun p => s₂ ⟨xc.1, p⟩))) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr × (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        let lhsSwap :
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          do
              let strat₂ ← Strategy.compWithRolesFlat xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              let cNext ← cpt₁ xc.1
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o))
        let rhsSwap :
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          do
              let cNext ← cpt₁ xc.1
              let strat₂ ← Strategy.compWithRolesFlat xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o))
        have hswap :=
          LawfulCommMonad.bind_comm
            (ma := Strategy.compWithRolesFlat xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid))
            (mb := cpt₁ xc.1)
            (k := fun strat₂ cNext =>
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o)))
        have hswap' : lhsSwap = rhsSwap := by
          simpa [lhsSwap, rhsSwap, bind_assoc] using hswap
        have hrhs :
            rhsSwap =
              cpt₁ xc.1 >>= fun cNext =>
                addPrefix <$>
                  (do
                    let strat₂ ←
                      Strategy.compWithRolesFlat xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
                    Strategy.runWithRoles
                      ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                      ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                      strat₂
                      (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o))) := by
          simp [rhsSwap]
        let lhsBody :
            (pairedSyntax m).Family Participant.counterpart (rest xc.1) (rRest xc.1)
              (fun tr => MidC ⟨xc.1, tr⟩) →
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          fun cNext =>
            addPrefix <$>
              (do
                let strat₂ ←
                  Strategy.compWithRolesFlat xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.appendFlat cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o)))
        let rhsBody :
            (pairedSyntax m).Family Participant.counterpart (rest xc.1) (rRest xc.1)
              (fun tr => MidC ⟨xc.1, tr⟩) →
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          fun cNext =>
            do
              let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles (rest xc.1) (rRest xc.1) xc.2 cNext
              let strat₂ ← f ⟨xc.1, tr₁⟩ mid
              let ⟨tr₂, outP, outC⟩ ←
                Strategy.runWithRoles
                  (s₂ ⟨xc.1, tr₁⟩) (r₂ ⟨xc.1, tr₁⟩) strat₂
                  (cpt₂ ⟨xc.1, tr₁⟩ out₁)
              pure ⟨⟨xc.1, Spec.Transcript.append (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩) tr₁ tr₂⟩,
                outP, outC⟩
        have hbody : lhsBody = rhsBody := by
          funext cNext
          simpa [lhsBody, rhsBody, bind_assoc, Spec.Transcript.append, addPrefix] using
            congrArg (fun z => addPrefix <$> z)
              (go (rest xc.1) (rRest xc.1)
                (s₂ := fun tr₁ => s₂ ⟨xc.1, tr₁⟩)
                (r₂ := fun tr₁ => r₂ ⟨xc.1, tr₁⟩)
                (OutputP := fun tr => OutputP ⟨xc.1, tr⟩)
                (OutputC := fun tr => OutputC ⟨xc.1, tr⟩)
                xc.2
                (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
                cNext
                (fun tr₁ out₁ => cpt₂ ⟨xc.1, tr₁⟩ out₁))
        simpa [rhsBody, addPrefix, Spec.Transcript.append, bind_assoc] using
          (hswap'.trans <| hrhs.trans <| congrArg (fun k => cpt₁ xc.1 >>= k) hbody)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [append, Decoration.append, bind_pure_comp]
        rw [Strategy.compWithRolesFlat.eq_3, Counterpart.appendFlat.eq_3]
        simp only [pure_bind]
        have hRunL := Strategy.runWithRoles_receiver
          (m := m)
          (X := _)
          (rest := fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))
          (rRest := fun x => (rRest x).append (fun p => r₂ ⟨x, p⟩))
          (OutputP := OutputP)
          (OutputC := OutputC)
          (fun x => do
            let next ← strat₁ x
            Strategy.compWithRolesFlat next (fun tr₁ mid => f ⟨x, tr₁⟩ mid))
          (do
            let ⟨x, next⟩ ← cpt₁
            pure ⟨x, Counterpart.appendFlat next (fun p o => cpt₂ ⟨x, p⟩ o)⟩)
        have hRunR := Strategy.runWithRoles_receiver
          (m := m)
          (X := _)
          (rest := rest)
          (rRest := rRest)
          (OutputP := MidP)
          (OutputC := MidC)
          strat₁ cpt₁
        rw [hRunL, hRunR]
        simp only [bind_assoc]
        refine congrArg (fun k => cpt₁ >>= k) ?_
        funext xc
        simp only [pure_bind]
        refine congrArg (fun k => strat₁ xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript ((rest xc.1).append (fun p => s₂ ⟨xc.1, p⟩))) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr × (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) × OutputP tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, Spec.Transcript.append, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1)
              (s₂ := fun tr₁ => s₂ ⟨xc.1, tr₁⟩)
              (r₂ := fun tr₁ => r₂ ⟨xc.1, tr₁⟩)
              (OutputP := fun tr => OutputP ⟨xc.1, tr⟩)
              (OutputC := fun tr => OutputC ⟨xc.1, tr⟩)
              next
              (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              xc.2
              (fun tr₁ out₁ => cpt₂ ⟨xc.1, tr₁⟩ out₁))
  exact go s₁ r₁ strat₁ f cpt₁ cpt₂

/-- Executing a factored composed strategy/counterpart (using `compWithRoles` and
`Counterpart.append`) factors into first executing the prefix interaction and then
executing the suffix continuation. Outputs are transported via `packAppend`. -/
theorem Strategy.runWithRoles_compWithRoles_append
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {MidP MidC : Spec.Transcript s₁ → Type u}
    {FP FC : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
    (strat₁ : Strategy.withRoles m s₁ r₁ MidP)
    (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
      m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁) (FP tr₁)))
    (cpt₁ : Counterpart m s₁ r₁ MidC)
    (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
      Counterpart m (s₂ tr₁) (r₂ tr₁) (FC tr₁)) :
    (do
      let strat ← Strategy.compWithRoles strat₁ f
      Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat
        (Counterpart.append cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC⟩ ←
          Strategy.runWithRoles (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
        pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂,
          Spec.Transcript.packAppend s₁ s₂ FP tr₁ tr₂ outP,
          Spec.Transcript.packAppend s₁ s₂ FC tr₁ tr₂ outC⟩) := by
  let rec go
      (s₁ : Spec) (r₁ : RoleDecoration s₁)
      {MidP MidC : Spec.Transcript s₁ → Type u}
      {s₂ : Spec.Transcript s₁ → Spec}
      {r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)}
      {FP FC : (tr₁ : Spec.Transcript s₁) → Spec.Transcript (s₂ tr₁) → Type u}
      (strat₁ : Strategy.withRoles m s₁ r₁ MidP)
      (f : (tr₁ : Spec.Transcript s₁) → MidP tr₁ →
        m (Strategy.withRoles m (s₂ tr₁) (r₂ tr₁) (FP tr₁)))
      (cpt₁ : Counterpart m s₁ r₁ MidC)
      (cpt₂ : (tr₁ : Spec.Transcript s₁) → MidC tr₁ →
        Counterpart m (s₂ tr₁) (r₂ tr₁) (FC tr₁)) :
      (do
        let strat ← Strategy.compWithRoles strat₁ f
        Strategy.runWithRoles (s₁.append s₂) (r₁.append r₂) strat
          (Counterpart.append cpt₁ cpt₂)) =
        (do
          let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles s₁ r₁ strat₁ cpt₁
          let strat₂ ← f tr₁ mid
          let ⟨tr₂, outP, outC⟩ ←
            Strategy.runWithRoles (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ out₁)
          pure ⟨Spec.Transcript.append s₁ s₂ tr₁ tr₂,
            Spec.Transcript.packAppend s₁ s₂ FP tr₁ tr₂ outP,
            Spec.Transcript.packAppend s₁ s₂ FC tr₁ tr₂ outC⟩) := by
    match s₁, r₁ with
    | .done, r₁ =>
        cases r₁
        simp [Strategy.compWithRoles, Counterpart.append,
          Strategy.runWithRoles_done, Spec.append, Spec.Decoration.append,
          Spec.Transcript.append, Spec.Transcript.packAppend, bind_pure_comp]
        have hId :
            (fun a : (tr : Spec.Transcript (s₂ PUnit.unit)) × FP PUnit.unit tr × FC PUnit.unit tr =>
              ⟨a.fst, (a.2.fst, a.2.snd)⟩) = id := by
          funext a
          cases a
          rfl
        simp [hId]
        rfl
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [append, Decoration.append, bind_pure_comp]
        rw [Strategy.compWithRoles.eq_2, Counterpart.append.eq_2]
        simp only [Strategy.runWithRoles_sender, pure_bind, bind_assoc]
        refine congrArg (fun k => strat₁ >>= k) ?_
        funext xc
        let addPrefix :
            ((tr : Spec.Transcript ((rest xc.1).append (fun p => s₂ ⟨xc.1, p⟩))) ×
              Spec.Transcript.liftAppend (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩)
                (fun tr₁ tr₂ => FP ⟨xc.1, tr₁⟩ tr₂) tr ×
              Spec.Transcript.liftAppend (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩)
                (fun tr₁ tr₂ => FC ⟨xc.1, tr₁⟩ tr₂) tr) →
            ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP tr ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        let lhsSwap :
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP tr ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC tr) := do
              let strat₂ ← Strategy.compWithRoles xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              let cNext ← cpt₁ xc.1
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.append cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o))
        let rhsSwap :
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP tr ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC tr) := do
              let cNext ← cpt₁ xc.1
              let strat₂ ← Strategy.compWithRoles xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.append cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o))
        have hswap :=
          LawfulCommMonad.bind_comm
            (ma := Strategy.compWithRoles xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid))
            (mb := cpt₁ xc.1)
            (k := fun strat₂ cNext =>
              addPrefix <$>
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.append cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o)))
        have hswap' : lhsSwap = rhsSwap := by
          simpa [lhsSwap, rhsSwap, bind_assoc] using hswap
        have hrhs :
            rhsSwap =
              cpt₁ xc.1 >>= fun cNext =>
                addPrefix <$>
                  (do
                    let strat₂ ←
                      Strategy.compWithRoles xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
                    Strategy.runWithRoles
                      ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                      ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                      strat₂
                      (Counterpart.append cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o))) := by
          simp [rhsSwap]
        let lhsBody :
            (pairedSyntax m).Family Participant.counterpart (rest xc.1) (rRest xc.1)
              (fun tr => MidC ⟨xc.1, tr⟩) →
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP tr ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC tr) :=
          fun cNext =>
            addPrefix <$>
              (do
                let strat₂ ←
                  Strategy.compWithRoles xc.2 (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
                Strategy.runWithRoles
                  ((rest xc.1).append fun p => s₂ ⟨xc.1, p⟩)
                  ((rRest xc.1).append fun p => r₂ ⟨xc.1, p⟩)
                  strat₂
                  (Counterpart.append cNext (fun p o => cpt₂ ⟨xc.1, p⟩ o)))
        let rhsBody :
            (pairedSyntax m).Family Participant.counterpart (rest xc.1) (rRest xc.1)
              (fun tr => MidC ⟨xc.1, tr⟩) →
            m ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP tr ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC tr) :=
          fun cNext =>
            do
              let ⟨tr₁, mid, out₁⟩ ← Strategy.runWithRoles (rest xc.1) (rRest xc.1) xc.2 cNext
              let strat₂ ← f ⟨xc.1, tr₁⟩ mid
              let ⟨tr₂, outP, outC⟩ ←
                Strategy.runWithRoles
                  (s₂ ⟨xc.1, tr₁⟩) (r₂ ⟨xc.1, tr₁⟩) strat₂
                  (cpt₂ ⟨xc.1, tr₁⟩ out₁)
              pure ⟨⟨xc.1, Spec.Transcript.append (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩) tr₁ tr₂⟩,
                Spec.Transcript.packAppend (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩)
                  (fun tr₁ tr₂ => FP ⟨xc.1, tr₁⟩ tr₂) tr₁ tr₂ outP,
                Spec.Transcript.packAppend (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩)
                  (fun tr₁ tr₂ => FC ⟨xc.1, tr₁⟩ tr₂) tr₁ tr₂ outC⟩
        have hbody : lhsBody = rhsBody := by
          funext cNext
          simpa [lhsBody, rhsBody, bind_assoc, Spec.Transcript.append,
            Spec.Transcript.packAppend, addPrefix] using
            congrArg (fun z => addPrefix <$> z)
              (go (rest xc.1) (rRest xc.1)
                (s₂ := fun tr₁ => s₂ ⟨xc.1, tr₁⟩)
                (r₂ := fun tr₁ => r₂ ⟨xc.1, tr₁⟩)
                (FP := fun tr₁ tr₂ => FP ⟨xc.1, tr₁⟩ tr₂)
                (FC := fun tr₁ tr₂ => FC ⟨xc.1, tr₁⟩ tr₂)
                xc.2
                (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
                cNext
                (fun tr₁ out₁ => cpt₂ ⟨xc.1, tr₁⟩ out₁))
        simpa [rhsBody, addPrefix, Spec.Transcript.append, Spec.Transcript.packAppend,
          bind_assoc] using
          (hswap'.trans <| hrhs.trans <| congrArg (fun k => cpt₁ xc.1 >>= k) hbody)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [append, Decoration.append, bind_pure_comp]
        rw [Strategy.compWithRoles.eq_3, Counterpart.append.eq_3]
        simp only [pure_bind]
        have hRunL := Strategy.runWithRoles_receiver
          (m := m)
          (X := _)
          (rest := fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))
          (rRest := fun x => (rRest x).append (fun p => r₂ ⟨x, p⟩))
          (OutputP := Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP)
          (OutputC := Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC)
          (fun x => do
            let next ← strat₁ x
            Strategy.compWithRoles next (fun tr₁ mid => f ⟨x, tr₁⟩ mid))
          (do
            let ⟨x, next⟩ ← cpt₁
            pure ⟨x, Counterpart.append next (fun p o => cpt₂ ⟨x, p⟩ o)⟩)
        have hRunR := Strategy.runWithRoles_receiver
          (m := m)
          (X := _)
          (rest := rest)
          (rRest := rRest)
          (OutputP := MidP)
          (OutputC := MidC)
          strat₁ cpt₁
        rw [hRunL, hRunR]
        simp only [bind_assoc]
        refine congrArg (fun k => cpt₁ >>= k) ?_
        funext xc
        simp only [pure_bind]
        refine congrArg (fun k => strat₁ xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript ((rest xc.1).append (fun p => s₂ ⟨xc.1, p⟩))) ×
              Spec.Transcript.liftAppend (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩)
                (fun tr₁ tr₂ => FP ⟨xc.1, tr₁⟩ tr₂) tr ×
              Spec.Transcript.liftAppend (rest xc.1) (fun p => s₂ ⟨xc.1, p⟩)
                (fun tr₁ tr₂ => FC ⟨xc.1, tr₁⟩ tr₂) tr) →
            ((tr : Spec.Transcript ((Spec.node _ rest).append s₂)) ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FP tr ×
              Spec.Transcript.liftAppend (Spec.node _ rest) s₂ FC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, Spec.Transcript.append, Spec.Transcript.packAppend,
          addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1)
              (s₂ := fun tr₁ => s₂ ⟨xc.1, tr₁⟩)
              (r₂ := fun tr₁ => r₂ ⟨xc.1, tr₁⟩)
              (FP := fun tr₁ tr₂ => FP ⟨xc.1, tr₁⟩ tr₂)
              (FC := fun tr₁ tr₂ => FC ⟨xc.1, tr₁⟩ tr₂)
              next
              (fun tr₁ mid => f ⟨xc.1, tr₁⟩ mid)
              xc.2
              (fun tr₁ out₁ => cpt₂ ⟨xc.1, tr₁⟩ out₁))
  exact go s₁ r₁ strat₁ f cpt₁ cpt₂

/-- Role swapping commutes with replication. -/
theorem RoleDecoration.swap_replicate {spec : Spec}
    (roles : RoleDecoration spec) (n : Nat) :
    (roles.replicate n).swap = (roles.swap).replicate n :=
  Spec.Decoration.map_replicate (fun _ => Role.swap) roles n

/-- `n`-fold counterpart iteration on `spec.replicate n`, threading state `β`
through each round. -/
def Counterpart.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {β : Type u} :
    (n : Nat) →
    (Fin n → β → Counterpart m spec roles (fun _ => β)) →
    β →
    Counterpart m (spec.replicate n) (roles.replicate n) (fun _ => β)
  | 0, _, b => b
  | n + 1, step, b =>
      Counterpart.appendFlat (step 0 b) (fun _ b' => iterate n (fun i => step i.succ) b')

/-- `n`-fold role-aware strategy iteration on `spec.replicate n`, threading state `α`
through each round. -/
def Strategy.iterateWithRoles {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α →
      m (Strategy.withRoles m spec roles (fun _ => α))) →
    α →
    m (Strategy.withRoles m (spec.replicate n) (roles.replicate n) (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    compWithRolesFlat strat (fun _ mid => iterateWithRoles n (fun i => step i.succ) mid)

end Spec

namespace Spec

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
      Counterpart m (spec i s) (roles i s) (fun tr => Family (i + 1) (advance i s tr))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    Counterpart m (Spec.stateChain Stage spec advance n i s)
      (Spec.Decoration.stateChain roles n i s) (Spec.Transcript.stateChainFamily Family n i s)
  | 0, _, _, b => b
  | n + 1, i, s, b =>
      Counterpart.append (step i s b)
        (fun tr b' => stateChainComp step n (i + 1) (advance i s tr) b')

/-- Compose role-aware strategies along a state chain with stage-dependent output.
At each stage, the step transforms `Family i s` into a strategy whose output is
`Family (i+1) (advance i s tr)`. The full state chain output is
`Transcript.stateChainFamily Family`. -/
def Strategy.stateChainCompWithRoles {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (Strategy.withRoles m (spec i s) (roles i s)
        (fun tr => Family (i + 1) (advance i s tr)))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    m (Strategy.withRoles m (Spec.stateChain Stage spec advance n i s)
      (Spec.Decoration.stateChain roles n i s) (Spec.Transcript.stateChainFamily Family n i s))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    compWithRoles strat
      (fun tr mid => stateChainCompWithRoles step n (i + 1) (advance i s tr) mid)

/-- Compose per-node-monad counterparts along a state chain with stage-dependent output.
At each stage, the step transforms `Family i s` into a counterpart whose output is
`Family (i+1) (advance i s tr)`. The full state chain output is
`Transcript.stateChainFamily Family`. -/
def Counterpart.withMonads.stateChainComp
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {md : (i : Nat) → (s : Stage i) → MonadDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      Counterpart.withMonads (spec i s) (roles i s) (md i s)
        (fun tr => Family (i + 1) (advance i s tr))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → Family i s →
    Counterpart.withMonads (Spec.stateChain Stage spec advance n i s)
      (Spec.Decoration.stateChain roles n i s)
      (Decoration.stateChain md n i s)
      (Spec.Transcript.stateChainFamily Family n i s)
  | 0, _, _, b => b
  | n + 1, i, s, b =>
      Counterpart.withMonads.append (step i s b)
        (fun tr b' => stateChainComp step n (i + 1) (advance i s tr) b')

end Spec
end Interaction
