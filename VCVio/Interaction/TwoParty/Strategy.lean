/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Syntax
import VCVio.Interaction.Basic.Ownership
import VCVio.Interaction.Basic.Interaction
import VCVio.Interaction.Basic.MonadDecoration
import VCVio.Interaction.TwoParty.Decoration
import VCVio.Interaction.TwoParty.Syntax
import VCVio.Interaction.Basic.Shape

/-!
# Role-dependent strategies and counterparts

Two-party strategies are `StrategyOver` specializations over role-decorated
interaction trees. The focal participant is the `Participant.focal` fiber of
`pairedSyntax`; owned nodes are effectful move/continuation packages, while
non-owned nodes respond to the counterpart's move. The counterpart participant
is the `Participant.counterpart` fiber of the same syntax.

The monadic variants add a `MonadDecoration`, so each node can use the effect
recorded in the decoration instead of one ambient monad. The same role
decoration still determines which participant owns each move.

This module also contains a public-coin counterpart syntax. An executable
counterpart samples a receiver move together with its continuation as one
opaque action; `Spec.TwoParty.PublicCoinCounterpart.syntax` exposes the sampler and
challenge-indexed continuation separately:

- `sample : m X` — how the next public challenge is chosen
- `next : (x : X) → ...` — how the rest of the verifier depends on that challenge

This is the structure needed for replay against a prescribed public transcript
while keeping execution itself in the ordinary two-party model.
-/

universe u

namespace Interaction
namespace Spec
namespace TwoParty

variable {m : Type u → Type u}
open _root_.Interaction.TwoParty

private def rolePerspective : Role → Participant.{u} → Ownership.Perspective
  | .sender, .focal => .owner
  | .sender, .counterpart => .observer
  | .receiver, .focal => .observer
  | .receiver, .counterpart => .owner

private def focalView (m : Type u → Type u) (X : Type u) :
    Ownership.LocalView X where
  own Cont := m ((x : X) × Cont x)
  other Cont := (x : X) → m (Cont x)

private def counterpartView (m : Type u → Type u) (X : Type u) :
    Ownership.LocalView X where
  own Cont := m ((x : X) × Cont x)
  other Cont := (x : X) → m (Cont x)

private def focalMonadicView (bm : BundledMonad.{u, u}) (X : Type u) :
    Ownership.LocalView X where
  own Cont := bm.M ((x : X) × Cont x)
  other Cont := (x : X) → bm.M (Cont x)

private def counterpartMonadicView (bm : BundledMonad.{u, u}) (X : Type u) :
    Ownership.LocalView X where
  own Cont := bm.M ((x : X) × Cont x)
  other Cont := (x : X) → bm.M (Cont x)

private def focalRunner (m : Type u → Type u) [Monad m] (X : Type u) :
    Ownership.LocalRunner m (focalView m X) where
  runOwn {Cont} (node : m ((x : X) × Cont x)) := node
  runOther {Cont} (node : (x : X) → m (Cont x)) x := node x

private def counterpartRunner (m : Type u → Type u) [Monad m] (X : Type u) :
    Ownership.LocalRunner m (counterpartView m X) where
  runOwn {Cont} (node : m ((x : X) × Cont x)) := node
  runOther {Cont} (node : (x : X) → m (Cont x)) x := node x

private def strategySyntax (m : Type u → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) where
  Node _ (X : Type u) (role : Role) (Cont : X → Type u) := role.Action m X Cont

private def SyntaxOver.forAgent {Agent : Type u} {Γ : Node.Context}
    (syn : SyntaxOver Agent Γ) (agent : Agent) :
    SyntaxOver PUnit Γ where
  Node _ X γ Cont := syn.Node agent X γ Cont

private theorem StrategyOver.forAgent {Agent : Type u} {Γ : Node.Context}
    (syn : SyntaxOver Agent Γ) (agent : Agent) :
    {spec : Spec} → {ctxs : Decoration Γ spec} → {Out : Transcript spec → Type u} →
    StrategyOver (SyntaxOver.forAgent syn agent) PUnit.unit spec ctxs Out =
      StrategyOver syn agent spec ctxs Out
  | .done, _, _ => rfl
  | .node _ next, ⟨γ, ctxs⟩, Out => by
      simp only [StrategyOver, SyntaxOver.forAgent]
      congr 1
      funext x
      exact StrategyOver.forAgent syn agent (spec := next x) (ctxs := ctxs x)
        (Out := fun tr => Out ⟨x, tr⟩)

private def counterpartFamilySyntax
    (Sender Receiver : (X : Type u) → (X → Type u) → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) where
  Node _ (X : Type u) (role : Role) (Cont : X → Type u) :=
    match role with
    | .sender => Sender X Cont
    | .receiver => Receiver X Cont

def pairedSyntax (m : Type u → Type u) :
    SyntaxOver.{u, u, u, 0} Participant.{u} (fun _ => Role) where
  Node agent X role Cont :=
    match agent, role with
    | .focal, .sender => m ((x : X) × Cont x)
    | .focal, .receiver => (x : X) → m (Cont x)
    | .counterpart, .sender => (x : X) → m (Cont x)
    | .counterpart, .receiver => m ((x : X) × Cont x)

private theorem pairedSyntax_eq_ownerBased (m : Type u → Type u) :
    pairedSyntax m =
      Ownership.syntaxOver (fun role agent => rolePerspective role agent) (fun {X} _role agent =>
        match agent with
        | .focal => focalView m X
        | .counterpart => counterpartView m X) := by
  apply congrArg SyntaxOver.mk
  funext agent X role Cont
  cases agent <;> cases role <;>
        simp [Ownership.LocalView.node, rolePerspective, focalView, counterpartView]

/-- Local execution law for the two participants of `pairedSyntax`.

At a sender node, the focal participant supplies the move and continuation,
while the counterpart observes that move. At a receiver node, the counterpart
supplies the move and continuation, while the focal participant observes it.
Together with `InteractionOver.run`, this is the canonical whole-protocol runner
for two-party role-decorated strategies.
-/
def pairedInteraction (m : Type u → Type u) [Monad m] :
    InteractionOver Participant.{u} (fun _ => Role) (pairedSyntax m) m where
  interact := fun {X} {γ : Role} {Cont} {Result} profile k =>
    match γ with
    | .sender => do
        let pNode : m ((x : X) × Cont Participant.focal x) := by
          simpa [pairedSyntax, Ownership.syntaxOver, rolePerspective, Participant.focal,
            focalView] using profile Participant.focal
        let cNode : (x : X) → m (Cont Participant.counterpart x) := by
          simpa [pairedSyntax, Ownership.syntaxOver, rolePerspective, Participant.focal,
            Participant.counterpart, counterpartView] using profile Participant.counterpart
        let ⟨x, pCont⟩ ← (focalRunner m X).runOwn pNode
        let cCont ← (counterpartRunner m X).runOther cNode x
        k x (fun
          | .focal => pCont
          | .counterpart => cCont)
    | .receiver => do
        let pNode : (x : X) → m (Cont Participant.focal x) := by
          simpa [pairedSyntax, Ownership.syntaxOver, rolePerspective, Participant.focal,
            Participant.counterpart, focalView] using profile Participant.focal
        let cNode : m ((x : X) × Cont Participant.counterpart x) := by
          simpa [pairedSyntax, Ownership.syntaxOver, rolePerspective, Participant.counterpart,
            counterpartView] using profile Participant.counterpart
        let ⟨x, cCont⟩ ← (counterpartRunner m X).runOwn cNode
        let pCont ← (focalRunner m X).runOther pNode x
        k x (fun
          | .focal => pCont
          | .counterpart => cCont)

/--
One-participant syntax for the focal side of a role-decorated tree with
per-node monads.

At sender nodes the focal participant owns the move and returns a message
together with the continuation in the node monad. At receiver nodes it observes
the counterpart's message and returns the continuation in the node monad.
-/
def focalMonadicSyntax :
    SyntaxOver.{u, 0, u, u + 1} PUnit RoleMonadContext where
  Node _ (X : Type u) γ (Cont : X → Type u) :=
    match γ with
    | ⟨role, bm⟩ => role.Action bm.M X Cont

/--
Functorial shape for the focal side of a role-decorated tree with per-node
monads.

The local node syntax is `focalMonadicSyntax`; the map operation transports
only recursive continuations, leaving the role, node monad, and selected move
unchanged.
-/
def focalMonadicShape :
    ShapeOver.{u, 0, u, u + 1} PUnit RoleMonadContext where
  toSyntaxOver := focalMonadicSyntax
  map := fun {agent} {X} {γ} {A} {B} f node =>
    match γ with
    | ⟨.sender, bm⟩ =>
        let send : bm.M ((x : X) × A x) := by
          simpa [focalMonadicSyntax] using node
        show focalMonadicSyntax.Node agent X ⟨.sender, bm⟩ B from
          ((fun xa => ⟨xa.1, f xa.1 xa.2⟩) <$> send : bm.M ((x : X) × B x))
    | ⟨.receiver, bm⟩ =>
        let observe : (x : X) → bm.M (A x) := by
          simpa [focalMonadicSyntax] using node
        show focalMonadicSyntax.Node agent X ⟨.receiver, bm⟩ B from
          (fun x => f x <$> observe x : (x : X) → bm.M (B x))

/--
One-participant syntax for the counterpart side of a role-decorated tree with
per-node monads.

At sender nodes the counterpart observes the focal participant's move. At
receiver nodes it owns the move and returns a message together with the
continuation in the node monad.
-/
def counterpartMonadicSyntax :
    SyntaxOver.{u, 0, u, u + 1} PUnit RoleMonadContext where
  Node _ (X : Type u) γ (Cont : X → Type u) :=
    match γ with
    | ⟨.sender, bm⟩ => (x : X) → bm.M (Cont x)
    | ⟨.receiver, bm⟩ => bm.M ((x : X) × Cont x)

/--
Functorial shape for the counterpart side of a role-decorated tree with
per-node monads.

The local node syntax is `counterpartMonadicSyntax`; the map operation
transports only recursive continuations, preserving the role, node monad, and
message/challenge choice.
-/
def counterpartMonadicShape :
    ShapeOver.{u, 0, u, u + 1} PUnit RoleMonadContext where
  toSyntaxOver := counterpartMonadicSyntax
  map := fun {agent} {X} {γ} {A} {B} f node =>
    match γ with
    | ⟨.sender, bm⟩ =>
        let observe : (x : X) → bm.M (A x) := by
          simpa [counterpartMonadicSyntax] using node
        show counterpartMonadicSyntax.Node agent X ⟨.sender, bm⟩ B from
          (fun x => f x <$> observe x : (x : X) → bm.M (B x))
    | ⟨.receiver, bm⟩ =>
        let receive : bm.M ((x : X) × A x) := by
          simpa [counterpartMonadicSyntax] using node
        show counterpartMonadicSyntax.Node agent X ⟨.receiver, bm⟩ B from
          ((fun xc => ⟨xc.1, f xc.1 xc.2⟩) <$> receive : bm.M ((x : X) × B x))

def pairedMonadicSyntax :
    SyntaxOver.{u, u, u, u + 1} Participant.{u} RolePairedMonadContext where
  Node agent X γ Cont :=
    match agent, γ with
    | .focal, ⟨.sender, ⟨bmP, _⟩⟩ => bmP.M ((x : X) × Cont x)
    | .focal, ⟨.receiver, ⟨bmP, _⟩⟩ => (x : X) → bmP.M (Cont x)
    | .counterpart, ⟨.sender, ⟨_, bmC⟩⟩ => (x : X) → bmC.M (Cont x)
    | .counterpart, ⟨.receiver, ⟨_, bmC⟩⟩ => bmC.M ((x : X) × Cont x)

private theorem pairedMonadicSyntax_eq_ownerBased :
    pairedMonadicSyntax =
      Ownership.syntaxOver (fun γ agent => rolePerspective γ.1 agent) (fun {X} γ agent =>
        match agent, γ with
        | .focal, ⟨_, ⟨bmP, _⟩⟩ => focalMonadicView bmP X
        | .counterpart, ⟨_, ⟨_, bmC⟩⟩ => counterpartMonadicView bmC X) := by
  apply congrArg SyntaxOver.mk
  funext agent X γ Cont
  cases agent <;> cases γ with
      | mk role bms =>
          cases role <;>
            simp [Ownership.LocalView.node, rolePerspective, focalMonadicView,
              counterpartMonadicView]

/-- A generic counterpart family parameterized by separate sender- and
receiver-side node representations.

Sender nodes model how the environment follows a move chosen by the focal
party. Receiver nodes model how the environment chooses a move itself. Both
ordinary counterpart syntax and replayable public-coin syntax are direct
`StrategyOver` specializations. -/
private def counterpartFamilyShape
    (Sender : (X : Type u) → (X → Type u) → Type u)
    (Receiver : (X : Type u) → (X → Type u) → Type u)
    (mapSender :
      {X : Type u} → {A B : X → Type u} →
      (∀ x, A x → B x) → Sender X A → Sender X B)
    (mapReceiver :
      {X : Type u} → {A B : X → Type u} →
      (∀ x, A x → B x) → Receiver X A → Receiver X B) :
    ShapeOver PUnit (fun _ => Role) where
  toSyntaxOver := counterpartFamilySyntax Sender Receiver
  map := fun {_agent} {_X} {γ} {_A} {_B} f node =>
    match γ with
    | .sender =>
        mapSender f node
    | .receiver =>
        mapReceiver f node

/-- Map a receiver-family output through a sender-owned sampled move. -/
def Counterpart.mapReceiver {m : Type u → Type u} [Functor m] :
    {X : Type u} → {A B : X → Type u} →
    (∀ x, A x → B x) → m ((x : X) × A x) → m ((x : X) × B x)
  | _, _, _, f, sample => (fun ⟨x, c⟩ => ⟨x, f x c⟩) <$> sample

/-- Map outputs through an effectful sender-side observation. -/
def Counterpart.mapSender {m : Type u → Type u} [Functor m] :
    {X : Type u} → {A B : X → Type u} →
    (∀ x, A x → B x) → ((x : X) → m (A x)) → ((x : X) → m (B x))
  | _, _, _, f, observe => fun x => f x <$> observe x

/-- Functorial output map for role-dependent strategies. -/
def Focal.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) →
      StrategyOver (pairedSyntax m) Participant.focal spec roles A →
      StrategyOver (pairedSyntax m) Participant.focal spec roles B
  | .done, _, _, _, f, a => f ⟨⟩ a
  | .node _ _, ⟨.sender, _⟩, _, _, f, send =>
      Counterpart.mapReceiver (fun x => mapOutput (fun p => f ⟨x, p⟩)) send
  | .node _ _, ⟨.receiver, _⟩, _, _, f, respond =>
      fun x => (mapOutput (fun p => f ⟨x, p⟩) ·) <$> respond x

/-- Pointwise identity on outputs is the identity on role-dependent strategies. -/
@[simp]
theorem Focal.mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : Transcript spec → Type u}
    (σ : StrategyOver (pairedSyntax m) Participant.focal spec roles A) :
    Focal.mapOutput (fun _ x => x) σ = σ := by
  match spec, roles with
  | .done, roles =>
      cases roles
      rfl
  | .node X rest, ⟨.sender, rRest⟩ =>
      let F :
          ((x : X) × StrategyOver (pairedSyntax m) Participant.focal
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) →
          ((x : X) × StrategyOver (pairedSyntax m) Participant.focal
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) :=
        fun xc => ⟨xc.1,
          Focal.mapOutput
            (fun (p : Transcript (rest xc.1)) (y : A ⟨xc.1, p⟩) => y) xc.2⟩
      have hpair : F = id := by
        funext xc
        cases xc with
        | mk x σ' =>
            simp only [F]
            rw [Focal.mapOutput_id]
            rfl
      rw [Focal.mapOutput, Counterpart.mapReceiver]
      change F <$> σ = σ
      rw [hpair]
      exact LawfulFunctor.id_map σ
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      funext x
      have hid :
          (mapOutput (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) :
              StrategyOver (pairedSyntax m) Participant.focal
                (rest x) (rRest x) (fun p => A ⟨x, p⟩) →
                StrategyOver (pairedSyntax m) Participant.focal
                  (rest x) (rRest x) (fun p => A ⟨x, p⟩)) =
            id := by
        funext s
        exact @mapOutput_id m _ _ (rest x) (rRest x) (fun p => A ⟨x, p⟩) s
      simp only [Focal.mapOutput, hid]
      exact LawfulFunctor.id_map (σ x)

/-- Functorial output map for counterparts. -/
def Counterpart.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) →
      StrategyOver (pairedSyntax m) Participant.counterpart spec roles A →
      StrategyOver (pairedSyntax m) Participant.counterpart spec roles B
  | .done, _, _, _, f, a => f ⟨⟩ a
  | .node _ _, ⟨.sender, _⟩, _, _, f, observe =>
      Counterpart.mapSender (fun x => mapOutput (fun p => f ⟨x, p⟩)) observe
  | .node _ _, ⟨.receiver, _⟩, _, _, f, receive =>
      Counterpart.mapReceiver (fun x => mapOutput (fun p => f ⟨x, p⟩)) receive

/-- A verifier counterpart with replayable public-coin receiver nodes.

An ordinary `StrategyOver (pairedSyntax m) Participant.counterpart` represents
a receiver node as an opaque monadic action returning both the sampled challenge
and the continuation. That is the right shape for execution, but it is too weak
for verifier-side Fiat-Shamir: given a prescribed challenge `x`, there is no
way to recover the continuation for `x` unless that continuation is exposed
separately.

`PublicCoinCounterpart.syntax` factors each receiver node into:
- `sample : m X` — how the verifier samples the next public challenge
- `next : (x : X) → ...` — how the rest of the verifier depends on that challenge

This is exactly the extra structure needed to replay a prescribed transcript
through the verifier. -/
def PublicCoinCounterpart.syntax (m : Type u → Type u) :
    SyntaxOver.{u, 0, u, 0} PUnit (fun _ => Role) :=
  counterpartFamilySyntax (fun X Cont => (x : X) → m (Cont x))
    (fun X Cont => m X × ((x : X) → Cont x))

namespace PublicCoinCounterpart

private def mapReceiver {m : Type u → Type u} :
    {X : Type u} → {A B : X → Type u} →
    (∀ x, A x → B x) → (m X × ((x : X) → A x)) → (m X × ((x : X) → B x))
  | _, _, _, f, ⟨sample, next⟩ => ⟨sample, fun x => f x (next x)⟩

private def publicCoinCounterpartShape (m : Type u → Type u) [Functor m] :
    ShapeOver PUnit (fun _ => Role) :=
  counterpartFamilyShape (fun X Cont => (x : X) → m (Cont x))
    (fun X Cont => m X × ((x : X) → Cont x))
    Counterpart.mapSender mapReceiver

/--
Local syntax-forgetting map from replayable public-coin counterparts to
ordinary executable counterparts.

At sender nodes the observer continuation is unchanged except for the recursive
translation. At receiver nodes the explicit sampler/continuation pair is
packed into the ordinary monadic action that samples a challenge and returns
the translated continuation for that challenge.
-/
def toCounterpartHom {m : Type u → Type u} [Monad m] :
    StrategyOver.Hom (PublicCoinCounterpart.syntax m) PUnit.unit
      (pairedSyntax m) Participant.counterpart where
  mapNode := fun {X} {γ} {A} {B} f node =>
    match γ with
    | .sender =>
        Counterpart.mapSender f node
    | .receiver =>
        let receiver : m X × ((x : X) → A x) := by
          simpa [PublicCoinCounterpart.syntax, counterpartFamilySyntax] using node
        show (pairedSyntax m).Node Participant.counterpart X .receiver B from
          do
            let x ← receiver.1
            pure ⟨x, f x (receiver.2 x)⟩

/-- Functorial output map for public-coin counterparts. The challenge samplers
are unchanged; only the terminal output carried by continuations is mapped. -/
def mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) →
    StrategyOver (PublicCoinCounterpart.syntax m) PUnit.unit spec roles A →
    StrategyOver (PublicCoinCounterpart.syntax m) PUnit.unit spec roles B :=
  fun {spec} {roles} {A} {B} f =>
    ShapeOver.mapOutput (publicCoinCounterpartShape m)
      (agent := PUnit.unit) (spec := spec) roles
      (A := A) (B := B) f

/-- Forget the public-coin factorization and recover the ordinary executable
counterpart. -/
def toCounterpart {m : Type u → Type u} [Monad m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {Output : Transcript spec → Type u} →
    StrategyOver (PublicCoinCounterpart.syntax m) PUnit.unit spec roles Output →
    StrategyOver (pairedSyntax m) Participant.counterpart spec roles Output
  :=
    fun {spec} {roles} {Output} =>
      StrategyOver.map toCounterpartHom
        (spec := spec) (ctxs := roles)
        (A := Output) (B := Output) (fun _ out => out)

/-- Replay a prescribed transcript through a public-coin counterpart. Sender
messages are read from the transcript; receiver samplers are ignored and the
stored continuation family is followed at the recorded challenge. -/
def replay {m : Type u → Type u} [Monad m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {Output : Transcript spec → Type u} →
    StrategyOver (PublicCoinCounterpart.syntax m) PUnit.unit spec roles Output →
    (tr : Transcript spec) → m (Output tr)
  | .done, _, _, c, _ => pure c
  | .node _ _, ⟨.sender, _⟩, _, observe, ⟨x, tr⟩ =>
      do
        let next ← observe x
        replay next tr
  | .node _ _, ⟨.receiver, _⟩, _, ⟨_, next⟩, ⟨x, tr⟩ =>
      replay (next x) tr

end PublicCoinCounterpart

/-- Pointwise identity on outputs is the identity on counterparts. -/
@[simp]
theorem Counterpart.mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : Transcript spec → Type u}
    (c : StrategyOver (pairedSyntax m) Participant.counterpart spec roles A) :
    Counterpart.mapOutput (fun _ x => x) c = c := by
  match spec, roles with
  | .done, roles =>
      cases roles
      simp [Counterpart.mapOutput]
  | .node _ rest, ⟨.sender, rRest⟩ =>
      funext x
      have hid :
          (Counterpart.mapOutput
            (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y) :
              StrategyOver (pairedSyntax m) Participant.counterpart
                (rest x) (rRest x) (fun p => A ⟨x, p⟩) →
                StrategyOver (pairedSyntax m) Participant.counterpart
                  (rest x) (rRest x) (fun p => A ⟨x, p⟩)) =
            id := by
        funext c'
        exact @Counterpart.mapOutput_id m _ _ (rest x) (rRest x) (fun p => A ⟨x, p⟩) c'
      change
        (Counterpart.mapOutput
          (fun (p : Transcript (rest x)) (y : A ⟨x, p⟩) => y)) <$> c x = c x
      rw [hid]
      exact LawfulFunctor.id_map (c x)
  | .node X rest, ⟨.receiver, rRest⟩ =>
      let F :
          ((x : X) × StrategyOver (pairedSyntax m) Participant.counterpart
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) →
          ((x : X) × StrategyOver (pairedSyntax m) Participant.counterpart
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) :=
        fun xc => ⟨xc.1,
          Counterpart.mapOutput
            (fun (p : Transcript (rest xc.1)) (y : A ⟨xc.1, p⟩) => y) xc.2⟩
      have hpair :
          F = id := by
        funext xc
        cases xc with
        | mk x c' =>
            simp only [F]
            rw [Counterpart.mapOutput_id]
            rfl
      rw [Counterpart.mapOutput, Counterpart.mapReceiver]
      change F <$> c = c
      rw [hpair]
      exact LawfulFunctor.id_map c

/-- Lift a deterministic counterpart into any monad.

At sender nodes the observational branch structure is unchanged. At receiver
nodes the chosen move and continuation are simply wrapped in `pure`. This is a
generic utility for reusing deterministic environments inside monadic execution
machinery built from `InteractionOver.run`. -/
def Counterpart.liftId {m : Type u → Type u} [Monad m] :
    {spec : Spec} → {roles : RoleDecoration spec} →
    {Output : Transcript spec → Type u} →
    StrategyOver (pairedSyntax Id) Participant.counterpart spec roles Output →
      StrategyOver (pairedSyntax m) Participant.counterpart spec roles Output
  | .done, _, _, c => c
  | .node _ _, ⟨.sender, _⟩, _, observe =>
      fun x => pure <| liftId (observe x)
  | .node _ _, ⟨.receiver, _⟩, _, ⟨x, c⟩ =>
      pure ⟨x, liftId c⟩

/-- The participant-indexed output family for a two-party run.

The focal participant carries `OutputP`, while the counterpart carries
`OutputC`. Naming this family gives the runner, profiles, and computation
rules a single canonical shape for participant outputs, which keeps dependent
function arguments definitionally aligned. -/
def participantOutputFamily
    {spec : Spec} (OutputP OutputC : Transcript spec → Type u)
    (agent : Participant.{u}) (tr : Transcript spec) : Type u :=
  match agent with
  | .focal => OutputP tr
  | .counterpart => OutputC tr

/-- Collect the two participant-indexed outputs into the result pair of a
two-party run. -/
def collectParticipantOutputs
    {spec : Spec} {OutputP OutputC : Transcript spec → Type u} :
    (tr : Transcript spec) →
      ((agent : Participant.{u}) → participantOutputFamily OutputP OutputC agent tr) →
      OutputP tr × OutputC tr :=
  fun _ out => (out Participant.focal, out Participant.counterpart)

/-- Assemble the focal strategy and counterpart strategy into a
participant-indexed profile for the generic runner. -/
def participantProfile
    {m : Type u → Type u} {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputC : Transcript spec → Type u}
    (strat : StrategyOver (pairedSyntax m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver (pairedSyntax m) Participant.counterpart spec roles OutputC) :
    (agent : Participant.{u}) →
      StrategyOver (pairedSyntax m) agent spec roles (participantOutputFamily OutputP OutputC agent)
  | .focal => strat
  | .counterpart => cpt

/-- Execute a focal/counterpart pair over a role-decorated interaction tree.

This is the generic `InteractionOver.run` specialized to `pairedSyntax`, with the
two participant fibers assembled by `participantProfile` and collected by
`collectParticipantOutputs`.
-/
def run {m : Type u → Type u} [Monad m]
    (spec : Spec) (roles : RoleDecoration spec)
    {OutputP : Transcript spec → Type u}
    {OutputC : Transcript spec → Type u}
    (strat : StrategyOver (pairedSyntax m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver (pairedSyntax m) Participant.counterpart spec roles OutputC) :
    m ((tr : Transcript spec) × OutputP tr × OutputC tr) :=
  InteractionOver.run (I := pairedInteraction m) roles (participantProfile strat cpt)
    collectParticipantOutputs

@[simp]
theorem InteractionOver.run_paired_done {m : Type u → Type u} [Monad m]
    {OutputP OutputC : Transcript Spec.done → Type u}
    (outP : OutputP ⟨⟩) (outC : OutputC ⟨⟩) :
    InteractionOver.run (I := pairedInteraction m) (spec := Spec.done) (ctxs := PUnit.unit)
      (participantProfile outP outC) collectParticipantOutputs =
      (pure ⟨⟨⟩, outP, outC⟩ :
        m ((tr : Transcript Spec.done) × OutputP tr × OutputC tr)) := by
  rfl

@[simp]
theorem InteractionOver.run_paired_sender {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : Transcript (Spec.node X rest) → Type u}
    (send :
      m ((x : X) × StrategyOver (pairedSyntax m) Participant.focal
        (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualFn : (x : X) → m (StrategyOver (pairedSyntax m) Participant.counterpart
      (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    InteractionOver.run (I := pairedInteraction m) (spec := Spec.node X rest)
      (ctxs := ⟨.sender, rRest⟩)
      (participantProfile
        (show StrategyOver (pairedSyntax m) Participant.focal
          (Spec.node X rest) ⟨.sender, rRest⟩ OutputP from send)
        (show StrategyOver (pairedSyntax m) Participant.counterpart
          (Spec.node X rest) ⟨.sender, rRest⟩ OutputC from dualFn))
      collectParticipantOutputs = (do
      let xc ← send
      let dualNext ← dualFn xc.1
      let tailOut ← InteractionOver.run (I := pairedInteraction m) (spec := rest xc.1)
        (ctxs := rRest xc.1)
        (participantProfile xc.2 dualNext) collectParticipantOutputs
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simp only [InteractionOver.run, pairedInteraction, pairedSyntax,
    participantOutputFamily, participantProfile, collectParticipantOutputs,
    focalRunner, counterpartRunner]
  apply congrArg (fun k => send >>= k)
  funext xc
  apply congrArg (fun k => dualFn xc.1 >>= k)
  funext dualNext
  rfl

@[simp]
theorem InteractionOver.run_paired_receiver {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : Transcript (Spec.node X rest) → Type u}
    (respond : (x : X) → m (StrategyOver (pairedSyntax m) Participant.focal
      (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualSample :
      m ((x : X) × StrategyOver (pairedSyntax m) Participant.counterpart
        (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    InteractionOver.run (I := pairedInteraction m) (spec := Spec.node X rest)
      (ctxs := ⟨.receiver, rRest⟩)
      (participantProfile
        (show StrategyOver (pairedSyntax m) Participant.focal
          (Spec.node X rest) ⟨.receiver, rRest⟩ OutputP from respond)
        (show StrategyOver (pairedSyntax m) Participant.counterpart
          (Spec.node X rest) ⟨.receiver, rRest⟩ OutputC from dualSample))
      collectParticipantOutputs = (do
      let xc ← dualSample
      let next ← respond xc.1
      let tailOut ← InteractionOver.run (I := pairedInteraction m) (spec := rest xc.1)
        (ctxs := rRest xc.1)
        (participantProfile next xc.2) collectParticipantOutputs
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simp only [InteractionOver.run, pairedInteraction, pairedSyntax,
    participantOutputFamily, participantProfile, collectParticipantOutputs,
    focalRunner, counterpartRunner]
  apply congrArg (fun k => dualSample >>= k)
  funext xc
  apply congrArg (fun k => respond xc.1 >>= k)
  funext next
  rfl

/-- Running a paired profile after mapping both participant outputs is the same
as running first and mapping the final triple. -/
theorem InteractionOver.run_paired_mapOutput_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputP' OutputC OutputC' : Transcript spec → Type u}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : StrategyOver (pairedSyntax m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver (pairedSyntax m) Participant.counterpart spec roles OutputC) :
    InteractionOver.run (I := pairedInteraction m) (spec := spec) (ctxs := roles)
      (participantProfile (Focal.mapOutput fP strat) (Counterpart.mapOutput fC cpt))
      collectParticipantOutputs =
      (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
        InteractionOver.run (I := pairedInteraction m) (spec := spec) (ctxs := roles)
          (participantProfile strat cpt) collectParticipantOutputs := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec)
      {OutputP OutputP' OutputC OutputC' : Transcript spec → Type u}
      (fP : ∀ tr, OutputP tr → OutputP' tr)
      (fC : ∀ tr, OutputC tr → OutputC' tr)
      (strat : StrategyOver (pairedSyntax m) Participant.focal spec roles OutputP)
      (cpt : StrategyOver (pairedSyntax m) Participant.counterpart spec roles OutputC) :
      InteractionOver.run (I := pairedInteraction m) (spec := spec) (ctxs := roles)
        (participantProfile (Focal.mapOutput fP strat) (Counterpart.mapOutput fC cpt))
        collectParticipantOutputs =
        (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
          InteractionOver.run (I := pairedInteraction m) (spec := spec) (ctxs := roles)
            (participantProfile strat cpt) collectParticipantOutputs := by
    match spec, roles with
    | .done, roles =>
        cases roles
        simp [Focal.mapOutput, Counterpart.mapOutput, InteractionOver.run_paired_done]
    | .node _ rest, ⟨.sender, rRest⟩ =>
        simp only [Focal.mapOutput, Counterpart.mapOutput, Counterpart.mapReceiver,
          Counterpart.mapSender]
        simp only [InteractionOver.run_paired_sender, bind_pure_comp, bind_map_left, map_bind,
          Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext xc
        refine congrArg (fun k => cpt xc.1 >>= k) ?_
        funext cNext
        let addPrefix :
            ((tr : Transcript (rest xc.1)) × (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Transcript (Spec.node _ rest)) × OutputP' tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [monad_norm, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (fun tr => fP ⟨xc.1, tr⟩) (fun tr => fC ⟨xc.1, tr⟩)
              xc.2 cNext)
    | .node _ rest, ⟨.receiver, rRest⟩ =>
        simp only [Focal.mapOutput, Counterpart.mapOutput,
          Counterpart.mapReceiver]
        simp only
          [InteractionOver.run_paired_receiver, bind_pure_comp, bind_map_left, map_bind,
            Functor.map_map]
        refine congrArg (fun k => cpt >>= k) ?_
        funext xc
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Transcript (rest xc.1)) × (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Transcript (Spec.node _ rest)) × OutputP' tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [monad_norm, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (fun tr => fP ⟨xc.1, tr⟩) (fun tr => fC ⟨xc.1, tr⟩)
              next xc.2)
  exact go spec roles fP fC strat cpt

@[simp]
theorem run_done {m : Type u → Type u} [Monad m]
    {OutputP OutputC : Transcript Spec.done → Type u}
    (outP : OutputP ⟨⟩) (outC : OutputC ⟨⟩) :
    run .done PUnit.unit outP outC =
      (pure ⟨⟨⟩, outP, outC⟩ :
        m ((tr : Transcript Spec.done) × OutputP tr × OutputC tr)) := by
  simp [run]

@[simp]
theorem run_sender {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : Transcript (Spec.node X rest) → Type u}
    (send :
      m ((x : X) × StrategyOver (pairedSyntax m) Participant.focal (rest x) (rRest x)
        (fun tr => OutputP ⟨x, tr⟩)))
    (dualFn : (x : X) → m (StrategyOver (pairedSyntax m) Participant.counterpart
      (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    run (Spec.node X rest) ⟨.sender, rRest⟩ send dualFn = (do
      let xc ← send
      let dualNext ← dualFn xc.1
      let tailOut ← run (rest xc.1) (rRest xc.1) xc.2 dualNext
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simp [run, InteractionOver.run_paired_sender]

@[simp]
theorem run_receiver {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : Transcript (Spec.node X rest) → Type u}
    (respond : (x : X) → m (StrategyOver (pairedSyntax m) Participant.focal
      (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualSample :
      m ((x : X) × StrategyOver (pairedSyntax m) Participant.counterpart
        (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    run (Spec.node X rest) ⟨.receiver, rRest⟩ respond dualSample = (do
      let xc ← dualSample
      let next ← respond xc.1
      let tailOut ← run (rest xc.1) (rRest xc.1) next xc.2
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simp [run, InteractionOver.run_paired_receiver]

theorem run_mapOutput_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputP' OutputC OutputC' : Transcript spec → Type u}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : StrategyOver (pairedSyntax m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver (pairedSyntax m) Participant.counterpart spec roles OutputC) :
    run spec roles (Focal.mapOutput fP strat)
      (Counterpart.mapOutput fC cpt) =
      (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
        run spec roles strat cpt := by
  simpa [run] using
    (InteractionOver.run_paired_mapOutput_mapOutput (m := m)
      fP fC strat cpt)

/--
View a strategy over a constant monad decoration as an ordinary single-monad
role strategy.
-/
def Focal.ofConstantMonads {m : Type u → Type u} [Monad m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output : Spec.Transcript spec → Type u} :
    StrategyOver focalMonadicSyntax PUnit.unit spec
      (RoleDecoration.withMonads roles (MonadDecoration.constant ⟨m, inferInstance⟩ spec))
      Output →
    StrategyOver (pairedSyntax m) Participant.focal spec roles Output :=
  match spec, roles with
  | .done, _ => fun strat => strat
  | .node _ rest, ⟨.sender, rRest⟩ =>
      fun strat =>
        Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              ofConstantMonads
                (rest msgAndRest.1) (rRest msgAndRest.1) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun strat x =>
        Functor.map (ofConstantMonads (rest x) (rRest x)) (strat x)

/--
View an ordinary single-monad role strategy as a strategy over a constant monad
decoration.
-/
def Focal.toConstantMonads {m : Type u → Type u} [Monad m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output : Spec.Transcript spec → Type u} :
    StrategyOver (pairedSyntax m) Participant.focal spec roles Output →
    StrategyOver focalMonadicSyntax PUnit.unit spec
      (RoleDecoration.withMonads roles (MonadDecoration.constant ⟨m, inferInstance⟩ spec))
      Output :=
  match spec, roles with
  | .done, _ => fun strat => strat
  | .node _ rest, ⟨.sender, rRest⟩ =>
      fun strat =>
        Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              toConstantMonads
                (rest msgAndRest.1) (rRest msgAndRest.1) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun strat x =>
        Functor.map (toConstantMonads (rest x) (rRest x)) (strat x)

/--
Lifting an ordinary role strategy into a constant monad decoration commutes
with output maps.

This is the naturality property used at boundaries that still accept ordinary
single-monad strategies while internal execution is phrased over nodewise
monad decorations.
-/
theorem Focal.toConstantMonads_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulFunctor m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output Output' : Spec.Transcript spec → Type u}
    (f : ∀ tr, Output tr → Output' tr)
    (strat : StrategyOver (pairedSyntax m) Participant.focal spec roles Output) :
    Focal.toConstantMonads spec roles
        (Focal.mapOutput f strat) =
      ShapeOver.mapOutput focalMonadicShape
        (agent := PUnit.unit)
        (spec := spec)
        (ctxs := RoleDecoration.withMonads roles
          (MonadDecoration.constant ⟨m, inferInstance⟩ spec))
        f
        (Focal.toConstantMonads spec roles strat) := by
  match spec, roles with
  | .done, _ =>
      rfl
  | .node _ rest, ⟨.sender, rRest⟩ =>
      simp only [Focal.mapOutput, Counterpart.mapReceiver,
        toConstantMonads, ShapeOver.mapOutput, focalMonadicShape,
        focalMonadicSyntax, RoleDecoration.withMonads, RoleDecoration.monadsOver,
        Spec.MonadDecoration.constant, Spec.Decoration.ofOver, Functor.map_map]
      apply congrArg (fun g => g <$> strat)
      funext msgAndRest
      rw [toConstantMonads_mapOutput
        (rest msgAndRest.1) (rRest msgAndRest.1)]
      rfl
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      funext x
      simp only [Focal.mapOutput, toConstantMonads,
        ShapeOver.mapOutput, focalMonadicShape, focalMonadicSyntax,
        RoleDecoration.withMonads, RoleDecoration.monadsOver,
        Spec.MonadDecoration.constant, Spec.Decoration.ofOver, Functor.map_map]
      apply congrArg (fun g => g <$> strat x)
      funext next
      rw [toConstantMonads_mapOutput (rest x) (rRest x)]
      rfl

/--
Retarget a monadic focal strategy along a nodewise monad homomorphism.

This traverses the strategy tree structurally, applying the supplied lift at
each node and recursing through the selected continuation.
-/
def Focal.mapMonadDecoration
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {md₁ md₂ : MonadDecoration spec}
    (hom : MonadDecoration.Hom spec md₁ md₂)
    {Output : Spec.Transcript spec → Type u} :
    StrategyOver focalMonadicSyntax PUnit.unit spec
      (RoleDecoration.withMonads roles md₁) Output →
    StrategyOver focalMonadicSyntax PUnit.unit spec
      (RoleDecoration.withMonads roles md₂) Output :=
  match spec, roles, md₁, md₂, hom with
  | .done, _, _, _, _ => fun strat => strat
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun strat =>
        lift <| Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              mapMonadDecoration (rest msgAndRest.1) (rRest msgAndRest.1)
                (homRest msgAndRest.1) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun strat x =>
        lift <| Functor.map
          (mapMonadDecoration (rest x) (rRest x) (homRest x)) (strat x)

/--
Retarget a monadic counterpart along a nodewise monad homomorphism.

This traverses the counterpart tree structurally, applying the supplied lift at
each node and recursing through the selected continuation.
-/
def Counterpart.mapMonadDecoration
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {md₁ md₂ : MonadDecoration spec}
    (hom : MonadDecoration.Hom spec md₁ md₂)
    {Output : Spec.Transcript spec → Type u} :
    StrategyOver counterpartMonadicSyntax PUnit.unit spec
      (RoleDecoration.withMonads roles md₁) Output →
    StrategyOver counterpartMonadicSyntax PUnit.unit spec
      (RoleDecoration.withMonads roles md₂) Output :=
  match spec, roles, md₁, md₂, hom with
  | .done, _, _, _, _ => fun cpt => cpt
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun cpt x =>
        lift <| Functor.map
          (mapMonadDecoration (rest x) (rRest x) (homRest x)) (cpt x)
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun cpt =>
        lift <| Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              mapMonadDecoration (rest msgAndRest.1) (rRest msgAndRest.1)
                (homRest msgAndRest.1) msgAndRest.2⟩)
          cpt

/-- One-step execution law for paired monadic two-party profiles.

At each node, the participant that owns the move runs in its decorated monad.
The supplied lifts embed the focal and counterpart node monads into the common
execution monad `m`; the resulting continuations are then passed to the generic
tree runner. -/
def pairedMonadicInteraction {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α) :
    InteractionOver Participant.{u} RolePairedMonadContext pairedMonadicSyntax m where
  interact := fun {X} {γ : RolePairedMonadContext X} {Cont} {Result} profile k =>
    match γ with
    | ⟨.sender, ⟨bmP, bmC⟩⟩ => do
        let pNode : bmP.M ((x : X) × Cont Participant.focal x) := by
          simpa [pairedMonadicSyntax, Ownership.syntaxOver, rolePerspective, Participant.focal,
            focalMonadicView] using profile Participant.focal
        let cNode : (x : X) → bmC.M (Cont Participant.counterpart x) := by
          simpa [pairedMonadicSyntax, Ownership.syntaxOver, rolePerspective, Participant.focal,
            Participant.counterpart, counterpartMonadicView] using profile Participant.counterpart
        let ⟨x, pCont⟩ ← liftStrat bmP pNode
        let cCont ← liftCpt bmC (cNode x)
        k x (fun
          | .focal => pCont
          | .counterpart => cCont)
    | ⟨.receiver, ⟨bmP, bmC⟩⟩ => do
        let ⟨x, cCont⟩ ← liftCpt bmC (profile Participant.counterpart)
        let pCont ← liftStrat bmP ((profile Participant.focal) x)
        k x (fun
          | .focal => pCont
          | .counterpart => cCont)

end TwoParty
end Spec
end Interaction
