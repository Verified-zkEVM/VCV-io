/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Ownership
import VCVio.Interaction.Basic.Interaction
import VCVio.Interaction.Basic.Shape
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

/-- Two-party paired syntax over an arbitrary lens-executed tree, parameterized
by an unbundled effect-like type constructor.

This is weaker than `monadicSyntax`: it records the same owner/observer node
shapes but does not require a `Monad` instance for `m`. Execution laws can add
that instance only at the point where effects are actually run. -/
def pairedSyntaxOver (m : Type uB₂ → Type uB₂) :
    SyntaxOver l Participant (fun _ : P.A => Role) where
  Node agent pos role Cont :=
    match agent, role with
    | .focal, .sender => m ((d : Q.B (l.toFunA pos)) × Cont d)
    | .focal, .receiver => (d : Q.B (l.toFunA pos)) → m (Cont d)
    | .counterpart, .sender => (d : Q.B (l.toFunA pos)) → m (Cont d)
    | .counterpart, .receiver => m ((d : Q.B (l.toFunA pos)) × Cont d)

/-- Functorial shape for `pairedSyntaxOver`. -/
def pairedShapeOver (m : Type uB₂ → Type uB₂) [Functor m] :
    Interaction.ShapeOver l Participant (fun _ : P.A => Role) where
  toSyntaxOver := (pairedSyntaxOver l m :
    SyntaxOver l Participant.{u} (fun _ : P.A => Role))
  map := fun {agent} {pos} {γ} {A} {B} f node =>
    match agent, γ with
    | Participant.focal, Role.sender =>
        let send : m ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [pairedSyntaxOver] using node
        ((fun da => ⟨da.1, f da.1 da.2⟩) <$> send :
          m ((d : Q.B (l.toFunA pos)) × B d))
    | Participant.focal, Role.receiver =>
        let observe : (d : Q.B (l.toFunA pos)) → m (A d) := by
          simpa [pairedSyntaxOver] using node
        fun d => f d <$> observe d
    | Participant.counterpart, Role.sender =>
        let observe : (d : Q.B (l.toFunA pos)) → m (A d) := by
          simpa [pairedSyntaxOver] using node
        fun d => f d <$> observe d
    | Participant.counterpart, Role.receiver =>
        let receive : m ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [pairedSyntaxOver] using node
        ((fun da => ⟨da.1, f da.1 da.2⟩) <$> receive :
          m ((d : Q.B (l.toFunA pos)) × B d))

/-- Local execution law for two participants of `pairedSyntaxOver`.

At sender nodes, the focal participant chooses the runtime direction. At
receiver nodes, the counterpart chooses it. The other participant follows the
chosen direction with its observer continuation. -/
def pairedInteractionOver (m : Type uB₂ → Type uB₂) [Monad m] :
    InteractionOver l Participant.{uB₂} (fun _ : P.A => Role)
      (pairedSyntaxOver l m) m where
  interact := fun {pos} {γ} {Cont} {_Result} profile k =>
    match γ with
    | .sender => do
        let pNode :
            m ((d : Q.B (l.toFunA pos)) × Cont Participant.focal d) := by
          simpa [pairedSyntaxOver] using profile Participant.focal
        let cNode :
            (d : Q.B (l.toFunA pos)) → m (Cont Participant.counterpart d) := by
          simpa [pairedSyntaxOver] using profile Participant.counterpart
        let ⟨d, pCont⟩ ← pNode
        let cCont ← cNode d
        k d (fun
          | .focal => pCont
          | .counterpart => cCont)
    | .receiver => do
        let pNode :
            (d : Q.B (l.toFunA pos)) → m (Cont Participant.focal d) := by
          simpa [pairedSyntaxOver] using profile Participant.focal
        let cNode :
            m ((d : Q.B (l.toFunA pos)) × Cont Participant.counterpart d) := by
          simpa [pairedSyntaxOver] using profile Participant.counterpart
        let ⟨d, cCont⟩ ← cNode
        let pCont ← pNode d
        k d (fun
          | .focal => pCont
          | .counterpart => cCont)

/-- Two-party monadic syntax over an arbitrary lens-executed control tree. -/
def monadicSyntax
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w}) :
    SyntaxOver l Participant (fun _ : P.A => Role) :=
  Ownership.monadicSyntax l (fun role agent => perspective role agent)
    (fun {pos} role agent => monad pos role agent)

/-- Functorial shape for two-party monadic syntax over a lens-executed tree. -/
def monadicShape
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w}) :
    Interaction.ShapeOver l Participant (fun _ : P.A => Role) where
  toSyntaxOver := monadicSyntax l monad
  map := fun {agent} {pos} {γ} {A} {B} f node =>
    match agent, γ with
    | Participant.focal, Role.sender =>
        let send :
            (monad pos Role.sender Participant.focal).M
              ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [monadicSyntax, Ownership.monadicSyntax, perspective] using node
        show (monadicSyntax l monad).Node Participant.focal pos Role.sender B from
          ((fun da => ⟨da.1, f da.1 da.2⟩) <$> send :
            (monad pos Role.sender Participant.focal).M
              ((d : Q.B (l.toFunA pos)) × B d))
    | Participant.focal, Role.receiver =>
        let observe :
            (d : Q.B (l.toFunA pos)) →
              (monad pos Role.receiver Participant.focal).M (A d) := by
          simpa [monadicSyntax, Ownership.monadicSyntax, perspective] using node
        show (monadicSyntax l monad).Node Participant.focal pos Role.receiver B from
          (fun d => f d <$> observe d)
    | Participant.counterpart, Role.sender =>
        let observe :
            (d : Q.B (l.toFunA pos)) →
              (monad pos Role.sender Participant.counterpart).M (A d) := by
          simpa [monadicSyntax, Ownership.monadicSyntax, perspective] using node
        show (monadicSyntax l monad).Node Participant.counterpart pos Role.sender B from
          (fun d => f d <$> observe d)
    | Participant.counterpart, Role.receiver =>
        let receive :
            (monad pos Role.receiver Participant.counterpart).M
              ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [monadicSyntax, Ownership.monadicSyntax, perspective] using node
        show (monadicSyntax l monad).Node Participant.counterpart pos Role.receiver B from
          ((fun da => ⟨da.1, f da.1 da.2⟩) <$> receive :
            (monad pos Role.receiver Participant.counterpart).M
              ((d : Q.B (l.toFunA pos)) × B d))

/--
Two-party syntax where the counterpart's owned moves are public coin.

Compared with `monadicSyntax`, only the counterpart-owned receiver node changes:
instead of an opaque `m ((d : Move) × Cont d)`, it stores
`m Move × ((d : Move) → Cont d)`. This exposes the continuation family needed
for replaying prescribed public challenges.
-/
def PublicCoinCounterpart.syntax
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

/-- Functorial shape for public-coin counterpart syntax over a lens-executed tree. -/
def PublicCoinCounterpart.shape
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂}) :
    Interaction.ShapeOver l Participant (fun _ : P.A => Role) where
  toSyntaxOver := PublicCoinCounterpart.syntax l monad
  map := fun {agent} {pos} {γ} {A} {B} f node =>
    match agent, γ with
    | Participant.focal, Role.sender =>
        let send :
            (monad pos Role.sender Participant.focal).M
              ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [PublicCoinCounterpart.syntax, Ownership.syntaxOver, perspective] using node
        show (PublicCoinCounterpart.syntax l monad).Node Participant.focal pos Role.sender B from
          ((fun da => ⟨da.1, f da.1 da.2⟩) <$> send :
            (monad pos Role.sender Participant.focal).M
              ((d : Q.B (l.toFunA pos)) × B d))
    | Participant.focal, Role.receiver =>
        let observe :
            (d : Q.B (l.toFunA pos)) →
              (monad pos Role.receiver Participant.focal).M (A d) := by
          simpa [PublicCoinCounterpart.syntax, Ownership.syntaxOver, perspective] using node
        show (PublicCoinCounterpart.syntax l monad).Node Participant.focal pos Role.receiver B from
          (fun d => f d <$> observe d)
    | Participant.counterpart, Role.sender =>
        let observe :
            (d : Q.B (l.toFunA pos)) →
              (monad pos Role.sender Participant.counterpart).M (A d) := by
          simpa [PublicCoinCounterpart.syntax, Ownership.syntaxOver, perspective] using node
        show (PublicCoinCounterpart.syntax l monad).Node
            Participant.counterpart pos Role.sender B from
          (fun d => f d <$> observe d)
    | Participant.counterpart, Role.receiver =>
        let receive :
            (monad pos Role.receiver Participant.counterpart).M (Q.B (l.toFunA pos)) ×
              ((d : Q.B (l.toFunA pos)) → A d) := by
          simpa [PublicCoinCounterpart.syntax, Ownership.syntaxOver, perspective] using node
        show (PublicCoinCounterpart.syntax l monad).Node
            Participant.counterpart pos Role.receiver B from
          ⟨receive.1, fun d => f d (receive.2 d)⟩

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
theorem PublicCoinCounterpart.syntax_focal_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (PublicCoinCounterpart.syntax l monad).Node Participant.focal pos Role.sender Cont =
      (monad pos Role.sender Participant.focal).M
        ((d : Q.B (l.toFunA pos)) × Cont d) :=
  rfl

@[simp]
theorem PublicCoinCounterpart.syntax_counterpart_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (PublicCoinCounterpart.syntax l monad).Node Participant.counterpart pos Role.sender Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.sender Participant.counterpart).M (Cont d)) :=
  rfl

@[simp]
theorem PublicCoinCounterpart.syntax_focal_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (PublicCoinCounterpart.syntax l monad).Node Participant.focal pos Role.receiver Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.receiver Participant.focal).M (Cont d)) :=
  rfl

@[simp]
theorem PublicCoinCounterpart.syntax_counterpart_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{uB₂, uB₂})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type uB₂) :
    (PublicCoinCounterpart.syntax l monad).Node Participant.counterpart pos Role.receiver Cont =
      ((monad pos Role.receiver Participant.counterpart).M (Q.B (l.toFunA pos)) ×
        ((d : Q.B (l.toFunA pos)) → Cont d)) :=
  rfl

end TwoParty
end Interaction
