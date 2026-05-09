/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Ownership
import VCVio.Interaction.Basic.Interaction
import VCVio.Interaction.Basic.Shape
import VCVio.Interaction.TwoParty.Decoration
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

/-- Spec-facing form of `perspective`, using the plain `Spec.Ownership` perspective type. -/
def perspectiveSpec (role : Role) (agent : Participant) : Spec.Ownership.Perspective :=
  match perspective role agent with
  | .owner => .owner
  | .observer => .observer

/-- Two-party paired syntax over an arbitrary lens-executed tree, parameterized
by an unbundled effect-like type constructor.

This is weaker than `SyntaxOver.TwoParty.monadic`: it records the same owner/observer node
shapes but does not require a `Monad` instance for `m`. Execution laws can add
that instance only at the point where effects are actually run. -/
def _root_.Interaction.SyntaxOver.TwoParty.paired (m : Type uB₂ → Type uB₂) :
    SyntaxOver l Participant (fun _ : P.A => Role) where
  Node agent pos role Cont :=
    match agent, role with
    | .focal, .sender => m ((d : Q.B (l.toFunA pos)) × Cont d)
    | .focal, .receiver => (d : Q.B (l.toFunA pos)) → m (Cont d)
    | .counterpart, .sender => (d : Q.B (l.toFunA pos)) → m (Cont d)
    | .counterpart, .receiver => m ((d : Q.B (l.toFunA pos)) × Cont d)

/-- Functorial shape for `SyntaxOver.TwoParty.paired`. -/
def _root_.Interaction.ShapeOver.TwoParty.paired (m : Type uB₂ → Type uB₂) [Functor m] :
    Interaction.ShapeOver l Participant (fun _ : P.A => Role) where
  toSyntaxOver := (SyntaxOver.TwoParty.paired l m :
    SyntaxOver l Participant.{u} (fun _ : P.A => Role))
  map := fun {agent} {pos} {γ} {A} {B} f node =>
    match agent, γ with
    | Participant.focal, Role.sender =>
        let send : m ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [SyntaxOver.TwoParty.paired] using node
        ((fun da => ⟨da.1, f da.1 da.2⟩) <$> send :
          m ((d : Q.B (l.toFunA pos)) × B d))
    | Participant.focal, Role.receiver =>
        let observe : (d : Q.B (l.toFunA pos)) → m (A d) := by
          simpa [SyntaxOver.TwoParty.paired] using node
        fun d => f d <$> observe d
    | Participant.counterpart, Role.sender =>
        let observe : (d : Q.B (l.toFunA pos)) → m (A d) := by
          simpa [SyntaxOver.TwoParty.paired] using node
        fun d => f d <$> observe d
    | Participant.counterpart, Role.receiver =>
        let receive : m ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [SyntaxOver.TwoParty.paired] using node
        ((fun da => ⟨da.1, f da.1 da.2⟩) <$> receive :
          m ((d : Q.B (l.toFunA pos)) × B d))

/-- Local execution law for two participants of `SyntaxOver.TwoParty.paired`.

At sender nodes, the focal participant chooses the runtime direction. At
receiver nodes, the counterpart chooses it. The other participant follows the
chosen direction with its observer continuation. -/
def _root_.Interaction.InteractionOver.TwoParty.paired
    (m : Type uB₂ → Type uB₂) [Monad m] :
    InteractionOver l Participant.{uB₂} (fun _ : P.A => Role)
      (SyntaxOver.TwoParty.paired l m) m where
  interact := fun {pos} {γ} {Cont} {_Result} profile k =>
    match γ with
    | .sender => do
        let pNode :
            m ((d : Q.B (l.toFunA pos)) × Cont Participant.focal d) := by
          simpa [SyntaxOver.TwoParty.paired] using profile Participant.focal
        let cNode :
            (d : Q.B (l.toFunA pos)) → m (Cont Participant.counterpart d) := by
          simpa [SyntaxOver.TwoParty.paired] using profile Participant.counterpart
        let ⟨d, pCont⟩ ← pNode
        let cCont ← cNode d
        k d (fun
          | .focal => pCont
          | .counterpart => cCont)
    | .receiver => do
        let pNode :
            (d : Q.B (l.toFunA pos)) → m (Cont Participant.focal d) := by
          simpa [SyntaxOver.TwoParty.paired] using profile Participant.focal
        let cNode :
            m ((d : Q.B (l.toFunA pos)) × Cont Participant.counterpart d) := by
          simpa [SyntaxOver.TwoParty.paired] using profile Participant.counterpart
        let ⟨d, cCont⟩ ← cNode
        let pCont ← pNode d
        k d (fun
          | .focal => pCont
          | .counterpart => cCont)

/-- Two-party monadic syntax over an arbitrary lens-executed control tree. -/
def _root_.Interaction.SyntaxOver.TwoParty.monadic
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w}) :
    SyntaxOver l Participant (fun _ : P.A => Role) :=
  Ownership.monadicSyntax l (fun role agent => perspective role agent)
    (fun {pos} role agent => monad pos role agent)

/-- Functorial shape for two-party monadic syntax over a lens-executed tree. -/
def _root_.Interaction.ShapeOver.TwoParty.monadic
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w}) :
    Interaction.ShapeOver l Participant (fun _ : P.A => Role) where
  toSyntaxOver := SyntaxOver.TwoParty.monadic l monad
  map := fun {agent} {pos} {γ} {A} {B} f node =>
    match agent, γ with
    | Participant.focal, Role.sender =>
        let send :
            (monad pos Role.sender Participant.focal).M
              ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [SyntaxOver.TwoParty.monadic, Ownership.monadicSyntax, perspective] using node
        show (SyntaxOver.TwoParty.monadic l monad).Node Participant.focal pos Role.sender B from
          ((fun da => ⟨da.1, f da.1 da.2⟩) <$> send :
            (monad pos Role.sender Participant.focal).M
              ((d : Q.B (l.toFunA pos)) × B d))
    | Participant.focal, Role.receiver =>
        let observe :
            (d : Q.B (l.toFunA pos)) →
              (monad pos Role.receiver Participant.focal).M (A d) := by
          simpa [SyntaxOver.TwoParty.monadic, Ownership.monadicSyntax, perspective] using node
        show (SyntaxOver.TwoParty.monadic l monad).Node Participant.focal pos Role.receiver B from
          (fun d => f d <$> observe d)
    | Participant.counterpart, Role.sender =>
        let observe :
            (d : Q.B (l.toFunA pos)) →
              (monad pos Role.sender Participant.counterpart).M (A d) := by
          simpa [SyntaxOver.TwoParty.monadic, Ownership.monadicSyntax, perspective] using node
        show
          (SyntaxOver.TwoParty.monadic l monad).Node
            Participant.counterpart pos Role.sender B from
          (fun d => f d <$> observe d)
    | Participant.counterpart, Role.receiver =>
        let receive :
            (monad pos Role.receiver Participant.counterpart).M
              ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [SyntaxOver.TwoParty.monadic, Ownership.monadicSyntax, perspective] using node
        show
          (SyntaxOver.TwoParty.monadic l monad).Node
            Participant.counterpart pos Role.receiver B from
          ((fun da => ⟨da.1, f da.1 da.2⟩) <$> receive :
            (monad pos Role.receiver Participant.counterpart).M
              ((d : Q.B (l.toFunA pos)) × B d))

/-- Two-party syntax over a paired focal/counterpart monad context. -/
def _root_.Interaction.SyntaxOver.TwoParty.pairedMonadic :
    SyntaxOver l Participant
      (RolePairedMonadContextOver.{uB₂, uA, uB} P) where
  Node agent pos γ Cont :=
    match agent, γ with
    | .focal, ⟨.sender, ⟨bmP, _⟩⟩ =>
        bmP.M ((d : Q.B (l.toFunA pos)) × Cont d)
    | .focal, ⟨.receiver, ⟨bmP, _⟩⟩ =>
        (d : Q.B (l.toFunA pos)) → bmP.M (Cont d)
    | .counterpart, ⟨.sender, ⟨_, bmC⟩⟩ =>
        (d : Q.B (l.toFunA pos)) → bmC.M (Cont d)
    | .counterpart, ⟨.receiver, ⟨_, bmC⟩⟩ =>
        bmC.M ((d : Q.B (l.toFunA pos)) × Cont d)

/-- Functorial shape for `SyntaxOver.TwoParty.pairedMonadic`. -/
def _root_.Interaction.ShapeOver.TwoParty.pairedMonadic :
    Interaction.ShapeOver l Participant
      (RolePairedMonadContextOver.{uB₂, uA, uB} P) where
  toSyntaxOver := SyntaxOver.TwoParty.pairedMonadic l
  map := fun {agent} {pos} {γ} {A} {B} f node =>
    match agent, γ with
    | Participant.focal, ⟨Role.sender, ⟨bmP, _⟩⟩ =>
        let send : bmP.M ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using node
        ((fun da => ⟨da.1, f da.1 da.2⟩) <$> send :
          bmP.M ((d : Q.B (l.toFunA pos)) × B d))
    | Participant.focal, ⟨Role.receiver, ⟨bmP, _⟩⟩ =>
        let observe : (d : Q.B (l.toFunA pos)) → bmP.M (A d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using node
        fun d => f d <$> observe d
    | Participant.counterpart, ⟨Role.sender, ⟨_, bmC⟩⟩ =>
        let observe : (d : Q.B (l.toFunA pos)) → bmC.M (A d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using node
        fun d => f d <$> observe d
    | Participant.counterpart, ⟨Role.receiver, ⟨_, bmC⟩⟩ =>
        let receive : bmC.M ((d : Q.B (l.toFunA pos)) × A d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using node
        ((fun da => ⟨da.1, f da.1 da.2⟩) <$> receive :
          bmC.M ((d : Q.B (l.toFunA pos)) × B d))

/-- One-step execution law for paired monadic two-party profiles over a lens. -/
def _root_.Interaction.InteractionOver.TwoParty.pairedMonadic
    {m : Type uB₂ → Type uB₂} [Monad m]
    (liftFocal : ∀ (bm : BundledMonad.{uB₂, uB₂}) {α : Type uB₂}, bm.M α → m α)
    (liftCounterpart : ∀ (bm : BundledMonad.{uB₂, uB₂}) {α : Type uB₂}, bm.M α → m α) :
    InteractionOver l Participant
      (RolePairedMonadContextOver.{uB₂, uA, uB} P)
      (SyntaxOver.TwoParty.pairedMonadic l) m where
  interact := fun {pos} {γ} {Cont} {_Result} profile k =>
    match γ with
    | ⟨.sender, ⟨bmP, bmC⟩⟩ => do
        let pNode :
            bmP.M ((d : Q.B (l.toFunA pos)) × Cont Participant.focal d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using profile Participant.focal
        let cNode :
            (d : Q.B (l.toFunA pos)) → bmC.M (Cont Participant.counterpart d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using profile Participant.counterpart
        let ⟨d, pCont⟩ ← liftFocal bmP pNode
        let cCont ← liftCounterpart bmC (cNode d)
        k d (fun
          | .focal => pCont
          | .counterpart => cCont)
    | ⟨.receiver, ⟨bmP, bmC⟩⟩ => do
        let cNode :
            bmC.M ((d : Q.B (l.toFunA pos)) × Cont Participant.counterpart d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using profile Participant.counterpart
        let pNode :
            (d : Q.B (l.toFunA pos)) → bmP.M (Cont Participant.focal d) := by
          simpa [SyntaxOver.TwoParty.pairedMonadic] using profile Participant.focal
        let ⟨d, cCont⟩ ← liftCounterpart bmC cNode
        let pCont ← liftFocal bmP (pNode d)
        k d (fun
          | .focal => pCont
          | .counterpart => cCont)

namespace PublicCoinCounterpart

/--
One-agent public-coin counterpart syntax over a lens-executed tree, parameterized
by an unbundled effect-like type constructor.

Sender nodes observe the focal side's move. Receiver nodes expose the sampler
and challenge-indexed continuation separately, which supports replay against a
prescribed public transcript.
-/
def _root_.Interaction.SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart
    (m : Type uB₂ → Type uB₂) :
    SyntaxOver l PUnit (fun _ : P.A => Role) where
  Node _ pos role Cont :=
    match role with
    | .sender => (d : Q.B (l.toFunA pos)) → m (Cont d)
    | .receiver => m (Q.B (l.toFunA pos)) × ((d : Q.B (l.toFunA pos)) → Cont d)

/-- Functorial shape for `SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart`. -/
def _root_.Interaction.ShapeOver.TwoParty.PublicCoinCounterpart.counterpart
    (m : Type uB₂ → Type uB₂) [Functor m] :
    ShapeOver l PUnit (fun _ : P.A => Role) where
  toSyntaxOver := SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart l m
  map := fun {_agent} {pos} {γ} {A} {_B} f node =>
    match γ with
    | .sender =>
        let observe : (d : Q.B (l.toFunA pos)) → m (A d) := by
          simpa [SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart] using node
        fun d => f d <$> observe d
    | .receiver =>
        let receive : m (Q.B (l.toFunA pos)) × ((d : Q.B (l.toFunA pos)) → A d) := by
          simpa [SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart] using node
        ⟨receive.1, fun d => f d (receive.2 d)⟩

/--
Local syntax-forgetting map from replayable public-coin counterparts to
ordinary executable counterparts over the same lens.
-/
def _root_.Interaction.StrategyOver.TwoParty.PublicCoinCounterpart.toCounterpartHom
    {m : Type uB₂ → Type uB₂} [Monad m] :
    StrategyOver.Hom
      (SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart l m) PUnit.unit
      (SyntaxOver.TwoParty.paired l m) Participant.counterpart where
  mapNode := fun {pos} {γ} {A} {B} f node =>
    match γ with
    | .sender =>
        let observe : (d : Q.B (l.toFunA pos)) → m (A d) := by
          simpa [SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart] using node
        (fun d => f d <$> observe d : (d : Q.B (l.toFunA pos)) → m (B d))
    | .receiver =>
        let receiver : m (Q.B (l.toFunA pos)) × ((d : Q.B (l.toFunA pos)) → A d) := by
          simpa [SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart] using node
        (do
            let d ← receiver.1
            pure ⟨d, f d (receiver.2 d)⟩ :
          m ((d : Q.B (l.toFunA pos)) × B d))

end PublicCoinCounterpart

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.monadic_focal_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (SyntaxOver.TwoParty.monadic l monad).Node Participant.focal pos Role.sender Cont =
      (monad pos Role.sender Participant.focal).M
        ((d : Q.B (l.toFunA pos)) × Cont d) :=
  rfl

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.monadic_counterpart_sender
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (SyntaxOver.TwoParty.monadic l monad).Node Participant.counterpart pos Role.sender Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.sender Participant.counterpart).M (Cont d)) :=
  rfl

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.monadic_focal_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (SyntaxOver.TwoParty.monadic l monad).Node Participant.focal pos Role.receiver Cont =
      ((d : Q.B (l.toFunA pos)) →
        (monad pos Role.receiver Participant.focal).M (Cont d)) :=
  rfl

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.monadic_counterpart_receiver
    (monad :
      (pos : P.A) → Role → Participant →
        BundledMonad.{max uB₂ w, max uB₂ w})
    (pos : P.A)
    (Cont : Q.B (l.toFunA pos) → Type (max uB₂ w)) :
    (SyntaxOver.TwoParty.monadic l monad).Node Participant.counterpart pos Role.receiver Cont =
      (monad pos Role.receiver Participant.counterpart).M
        ((d : Q.B (l.toFunA pos)) × Cont d) :=
  rfl

end TwoParty
end Interaction
