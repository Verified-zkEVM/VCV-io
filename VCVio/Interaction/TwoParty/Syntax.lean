/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Ownership
import VCVio.Interaction.TwoParty.Role

/-!
# Two-party syntax over lens-executed trees

This module provides the two-party ownership profile and common local syntax
specializations over the generic `Interaction.SyntaxOver` core.

It intentionally does not define another recursive strategy hierarchy:
whole-tree participant types are always obtained from `StrategyOver`.
-/

@[expose] public section

universe u uA uB uA₂ uB₂ w

namespace Interaction
namespace TwoParty

open PFunctor

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
variable (l : PFunctor.Lens P Q)

/-- The two agents in a focused two-party interaction. -/
inductive Participant : Type u where
  | focal
  | counterpart
  deriving DecidableEq

/-- Ownership perspective induced by a sender/receiver role. -/
def perspective : Role → Participant → Ownership.Perspective
  | .sender, .focal => .owner
  | .sender, .counterpart => .observer
  | .receiver, .focal => .observer
  | .receiver, .counterpart => .owner

/-- Two-party monadic syntax over an arbitrary lens-executed control tree. -/
def monadicSyntax
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w}) :
    SyntaxOver l Participant (fun _ : P.A => Role) :=
  Ownership.monadicSyntax l (fun role agent => perspective role agent)
    (fun {pos} role agent => monad pos role agent)

/--
Two-party syntax where the counterpart's owned moves are public coin.

Compared with `monadicSyntax`, only the counterpart-owned receiver node changes:
instead of an opaque `m ((d : Move) × Cont d)`, it stores
`m Move × ((d : Move) → Cont d)`. This exposes the continuation family needed
for replaying prescribed public challenges.
-/
def publicCoinCounterpartSyntax
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂}) :
    SyntaxOver l Participant (fun _ : P.A => Role) :=
  Ownership.syntaxOver l (fun role agent => perspective role agent)
    (fun {pos} role agent =>
      match agent with
      | Participant.focal =>
          Ownership.LocalView.monadic (monad pos role Participant.focal) (Q.B (l.toFunA pos))
      | Participant.counterpart =>
          Ownership.LocalView.publicCoin (monad pos role Participant.counterpart)
            (Q.B (l.toFunA pos)))

@[simp]
theorem monadicSyntax_focal_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (monadicSyntax l monad).Node Participant.focal pos Role.sender Cont =
      (monad pos Role.sender Participant.focal).M
        ((d : Q.B (l.toFunA pos)) × Cont d) :=
  rfl

@[simp]
theorem monadicSyntax_counterpart_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (monadicSyntax l monad).Node Participant.counterpart pos Role.sender Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.sender Participant.counterpart).M (Cont d)) :=
  rfl

@[simp]
theorem monadicSyntax_focal_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (monadicSyntax l monad).Node Participant.focal pos Role.receiver Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.receiver Participant.focal).M (Cont d)) :=
  rfl

@[simp]
theorem monadicSyntax_counterpart_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (monadicSyntax l monad).Node Participant.counterpart pos Role.receiver Cont =
      (monad pos Role.receiver Participant.counterpart).M
        ((d : Q.B (l.toFunA pos)) × Cont d) :=
  rfl

@[simp]
theorem publicCoinCounterpartSyntax_focal_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (publicCoinCounterpartSyntax l monad).Node Participant.focal pos Role.sender Cont =
      (monad pos Role.sender Participant.focal).M
        ((d : Q.B (l.toFunA pos)) × Cont d) :=
  rfl

@[simp]
theorem publicCoinCounterpartSyntax_counterpart_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (publicCoinCounterpartSyntax l monad).Node Participant.counterpart pos Role.sender Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.sender Participant.counterpart).M (Cont d)) :=
  rfl

@[simp]
theorem publicCoinCounterpartSyntax_focal_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (publicCoinCounterpartSyntax l monad).Node Participant.focal pos Role.receiver Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.receiver Participant.focal).M (Cont d)) :=
  rfl

@[simp]
theorem publicCoinCounterpartSyntax_counterpart_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (publicCoinCounterpartSyntax l monad).Node Participant.counterpart pos Role.receiver Cont =
      ((monad pos Role.receiver Participant.counterpart).M (Q.B (l.toFunA pos)) ×
        ((d : Q.B (l.toFunA pos)) → Cont d)) :=
  rfl

end TwoParty
end Interaction
