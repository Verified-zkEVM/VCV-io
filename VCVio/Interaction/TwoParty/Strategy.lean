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
`SyntaxOver.TwoParty.pairedSpec`; owned nodes are effectful move/continuation packages, while
non-owned nodes respond to the counterpart's move. The counterpart participant
is the `Participant.counterpart` fiber of the same syntax.

The monadic variants add a `Spec.MonadDecoration`, so each node can use the effect
recorded in the decoration instead of one ambient monad. The same role
decoration still determines which participant owns each move.

This module also contains a public-coin counterpart syntax. An executable
counterpart samples a receiver move together with its continuation as one
opaque action; `SyntaxOver.TwoParty.PublicCoinCounterpart.counterpartSpec` exposes the
sampler and challenge-indexed continuation separately:

- `sample : m X` — how the next public challenge is chosen
- `next : (x : X) → ...` — how the rest of the verifier depends on that challenge

This is the structure needed for replay against a prescribed public transcript
while keeping execution itself in the ordinary two-party model.
-/

universe u

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace TwoParty

variable {m : Type u → Type u}
open TwoParty

def _root_.Interaction.SyntaxOver.TwoParty.pairedSpec (m : Type u → Type u) :
    SyntaxOver
      (PFunctor.Lens.id Spec.basePFunctor) Participant.{u} (fun _ => Role) :=
  SyntaxOver.TwoParty.paired (PFunctor.Lens.id Spec.basePFunctor) m

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.pairedSpec_focal_sender
    (m : Type u → Type u) (X : Type u) (Cont : X → Type u) :
    (SyntaxOver.TwoParty.pairedSpec m).Node Participant.focal X Role.sender Cont =
      m ((x : X) × Cont x) :=
  rfl

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.pairedSpec_focal_receiver
    (m : Type u → Type u) (X : Type u) (Cont : X → Type u) :
    (SyntaxOver.TwoParty.pairedSpec m).Node Participant.focal X Role.receiver Cont =
      ((x : X) → m (Cont x)) :=
  rfl

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.pairedSpec_counterpart_sender
    (m : Type u → Type u) (X : Type u) (Cont : X → Type u) :
    (SyntaxOver.TwoParty.pairedSpec m).Node Participant.counterpart X Role.sender Cont =
      ((x : X) → m (Cont x)) :=
  rfl

@[simp]
theorem _root_.Interaction.SyntaxOver.TwoParty.pairedSpec_counterpart_receiver
    (m : Type u → Type u) (X : Type u) (Cont : X → Type u) :
    (SyntaxOver.TwoParty.pairedSpec m).Node Participant.counterpart X Role.receiver Cont =
      m ((x : X) × Cont x) :=
  rfl

theorem _root_.Interaction.SyntaxOver.TwoParty.pairedSpec_eq_ownerBased (m : Type u → Type u) :
    SyntaxOver.TwoParty.pairedSpec m =
      Spec.Ownership.syntaxOver
        (fun role agent => perspectiveSpec role agent)
        (fun {X} _role _agent =>
          { own := fun Cont => m ((x : X) × Cont x)
            other := fun Cont => (x : X) → m (Cont x) }) := by
  apply congrArg Interaction.SyntaxOver.mk
  funext agent X role Cont
  cases agent <;> cases role <;>
        simp [PFunctor.Lens.id, Spec.Ownership.LocalView.node, perspective, perspectiveSpec]

/-- Functorial shape for the ordinary paired two-party syntax over plain specs. -/
def _root_.Interaction.ShapeOver.TwoParty.pairedSpec (m : Type u → Type u) [Functor m] :
    ShapeOver
      (PFunctor.Lens.id Spec.basePFunctor) Participant.{u} (fun _ => Role) :=
  ShapeOver.TwoParty.paired (PFunctor.Lens.id Spec.basePFunctor) m

/-- Local execution law for the two participants of `SyntaxOver.TwoParty.pairedSpec`.

At a sender node, the focal participant supplies the move and continuation,
while the counterpart observes that move. At a receiver node, the counterpart
supplies the move and continuation, while the focal participant observes it.
Together with `InteractionOver.run`, this is the canonical whole-protocol runner
for two-party role-decorated strategies.
-/
def _root_.Interaction.InteractionOver.TwoParty.pairedSpec (m : Type u → Type u) [Monad m] :
    InteractionOver
      (PFunctor.Lens.id Spec.basePFunctor) Participant.{u} (fun _ => Role)
      (SyntaxOver.TwoParty.pairedSpec m) m :=
  InteractionOver.TwoParty.paired (PFunctor.Lens.id Spec.basePFunctor) m

def _root_.Interaction.SyntaxOver.TwoParty.pairedMonadicSpec :
    SyntaxOver
      (PFunctor.Lens.id Spec.basePFunctor) Participant.{u} RolePairedMonadContext :=
  SyntaxOver.TwoParty.pairedMonadic (PFunctor.Lens.id Spec.basePFunctor)

/-- Functorial shape for paired role/monad two-party syntax over plain specs. -/
def _root_.Interaction.ShapeOver.TwoParty.pairedMonadicSpec :
    ShapeOver
      (PFunctor.Lens.id Spec.basePFunctor) Participant.{u} RolePairedMonadContext :=
  ShapeOver.TwoParty.pairedMonadic (PFunctor.Lens.id Spec.basePFunctor)

/--
One-participant syntax for the focal side of a role-decorated tree with
per-node monads.

At sender nodes the focal participant owns the move and returns a message
together with the continuation in the node monad. At receiver nodes it observes
the counterpart's message and returns the continuation in the node monad.
-/
def _root_.Interaction.SyntaxOver.TwoParty.Focal.monadicSpec :
    SyntaxOver
      (PFunctor.Lens.id Spec.basePFunctor) PUnit RoleMonadContext :=
  SyntaxOver.comap RoleMonadContext.diagonal
    (SyntaxOver.forAgent SyntaxOver.TwoParty.pairedMonadicSpec
      (Participant.focal : Participant.{u}))

/--
Functorial shape for the focal side of a role-decorated tree with per-node
monads.

The local node syntax is `SyntaxOver.TwoParty.Focal.monadicSpec`; the map operation transports
only recursive continuations, leaving the role, node monad, and selected move
unchanged.
-/
def _root_.Interaction.ShapeOver.TwoParty.Focal.monadicSpec :
    ShapeOver
      (PFunctor.Lens.id Spec.basePFunctor) PUnit RoleMonadContext :=
  ShapeOver.comap RoleMonadContext.diagonal
    (ShapeOver.forAgent ShapeOver.TwoParty.pairedMonadicSpec
      (Participant.focal : Participant.{u}))

/--
One-participant syntax for the counterpart side of a role-decorated tree with
per-node monads.

At sender nodes the counterpart observes the focal participant's move. At
receiver nodes it owns the move and returns a message together with the
continuation in the node monad.
-/
def _root_.Interaction.SyntaxOver.TwoParty.Counterpart.monadicSpec :
    SyntaxOver
      (PFunctor.Lens.id Spec.basePFunctor) PUnit RoleMonadContext :=
  SyntaxOver.comap RoleMonadContext.diagonal
    (SyntaxOver.forAgent SyntaxOver.TwoParty.pairedMonadicSpec
      (Participant.counterpart : Participant.{u}))

/--
Functorial shape for the counterpart side of a role-decorated tree with
per-node monads.

The local node syntax is `SyntaxOver.TwoParty.Counterpart.monadicSpec`; the map operation
transports only recursive continuations, preserving the role, node monad, and
message/challenge choice.
-/
def _root_.Interaction.ShapeOver.TwoParty.Counterpart.monadicSpec :
    ShapeOver
      (PFunctor.Lens.id Spec.basePFunctor) PUnit RoleMonadContext :=
  ShapeOver.comap RoleMonadContext.diagonal
    (ShapeOver.forAgent ShapeOver.TwoParty.pairedMonadicSpec
      (Participant.counterpart : Participant.{u}))

theorem _root_.Interaction.SyntaxOver.TwoParty.pairedMonadicSpec_eq_ownerBased :
    SyntaxOver.TwoParty.pairedMonadicSpec =
      Spec.Ownership.syntaxOver (fun γ agent => perspectiveSpec γ.1 agent) (fun {X} γ agent =>
        match agent, γ with
        | .focal, ⟨_, ⟨bmP, _⟩⟩ => Spec.Ownership.LocalView.monadic bmP X
        | .counterpart, ⟨_, ⟨_, bmC⟩⟩ => Spec.Ownership.LocalView.monadic bmC X) := by
  apply congrArg Interaction.SyntaxOver.mk
  funext agent X γ Cont
  cases agent <;> cases γ with
      | mk role bms =>
          cases role <;>
            simp [PFunctor.Lens.id, Spec.Ownership.LocalView.node, perspective, perspectiveSpec,
              Spec.Ownership.LocalView.monadic]

/-- Functorial output map for role-dependent strategies. -/
def _root_.Interaction.StrategyOver.TwoParty.Focal.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : PFunctor.FreeM.Path spec → Type u} →
    (∀ tr, A tr → B tr) →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles A →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles B
  := fun {spec} {roles} {A} {B} f =>
    ShapeOver.mapOutput (ShapeOver.TwoParty.pairedSpec m)
      (agent := Participant.focal)
      (spec := spec)
      (ctxs := roles)
      (A := A) (B := B)
      f

/-- Pointwise identity on outputs is the identity on role-dependent strategies. -/
@[simp]
theorem _root_.Interaction.StrategyOver.TwoParty.Focal.mapOutput_id
    {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : PFunctor.FreeM.Path spec → Type u}
    (σ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles A) :
    StrategyOver.TwoParty.Focal.mapOutput (fun _ x => x) σ = σ := by
  match spec, roles with
  | .done, roles =>
      cases roles
      rfl
  | .node X rest, ⟨.sender, rRest⟩ =>
      let F :
          ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) →
          ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) :=
        fun xc => ⟨xc.1,
          StrategyOver.TwoParty.Focal.mapOutput
            (fun (p : PFunctor.FreeM.Path (rest xc.1)) (y : A ⟨xc.1, p⟩) => y) xc.2⟩
      have hpair : F = id := by
        funext xc
        cases xc with
        | mk x σ' =>
            simp only [F]
            have h :
                StrategyOver.TwoParty.Focal.mapOutput
                  (fun (p : PFunctor.FreeM.Path (rest x)) (y : A ⟨x, p⟩) => y) σ' = σ' := by
              simpa using
                (@StrategyOver.TwoParty.Focal.mapOutput_id m _ _
                  (rest x) (rRest x) (fun p => A ⟨x, p⟩) σ')
            exact Sigma.ext rfl (heq_of_eq h)
      simp only [StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired, PFunctor.Lens.id]
      change F <$> σ = σ
      rw [hpair]
      exact LawfulFunctor.id_map σ
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      funext x
      have hid : ∀ s : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
            (rest x) (rRest x) (fun p => A ⟨x, p⟩),
          StrategyOver.TwoParty.Focal.mapOutput
            (fun (p : PFunctor.FreeM.Path (rest x)) (y : A ⟨x, p⟩) => y) s = s :=
        fun s =>
          @StrategyOver.TwoParty.Focal.mapOutput_id m _ _
            (rest x) (rRest x) (fun p => A ⟨x, p⟩) s
      simp only [StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired, PFunctor.Lens.id]
      calc (StrategyOver.TwoParty.Focal.mapOutput
              (fun (p : PFunctor.FreeM.Path (rest x)) (y : A ⟨x, p⟩) => y) ·) <$> σ x
          = id <$> σ x := by congr 1; funext s; exact hid s
        _ = σ x := LawfulFunctor.id_map (σ x)

/-- Functorial output map for counterparts. -/
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.mapOutput
    {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : PFunctor.FreeM.Path spec → Type u} →
    (∀ tr, A tr → B tr) →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles A →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles B
  := fun {spec} {roles} {A} {B} f =>
    ShapeOver.mapOutput (ShapeOver.TwoParty.pairedSpec m)
      (agent := Participant.counterpart)
      (spec := spec)
      (ctxs := roles)
      (A := A) (B := B)
      f

namespace PublicCoinCounterpart

/-- A verifier counterpart with replayable public-coin receiver nodes.

An ordinary `StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart` represents
a receiver node as an opaque monadic action returning both the sampled challenge
and the continuation. That is the right shape for execution, but it is too weak
for verifier-side Fiat-Shamir: given a prescribed challenge `x`, there is no
way to recover the continuation for `x` unless that continuation is exposed
separately.

`SyntaxOver.TwoParty.PublicCoinCounterpart.counterpartSpec` factors each receiver node into:
- `sample : m X` — how the verifier samples the next public challenge
- `next : (x : X) → ...` — how the rest of the verifier depends on that challenge

This is exactly the extra structure needed to replay a prescribed transcript
through the verifier. -/
def counterpartSyntax (m : Type u → Type u) :
    SyntaxOver
      (PFunctor.Lens.id Spec.basePFunctor) PUnit (fun _ => Role) :=
  SyntaxOver.TwoParty.PublicCoinCounterpart.counterpart (PFunctor.Lens.id Spec.basePFunctor) m

/--
Local syntax-forgetting map from replayable public-coin counterparts to
ordinary executable counterparts.

At sender nodes the observer continuation is unchanged except for the recursive
translation. At receiver nodes the explicit sampler/continuation pair is
packed into the ordinary monadic action that samples a challenge and returns
the translated continuation for that challenge.
-/
def toCounterpartHom {m : Type u → Type u} [Monad m] :
    StrategyOver.Hom (counterpartSyntax m) PUnit.unit
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart :=
  StrategyOver.TwoParty.PublicCoinCounterpart.toCounterpartHom
    (PFunctor.Lens.id Spec.basePFunctor)

/-- Functorial output map for public-coin counterparts. The challenge samplers
are unchanged; only the terminal output carried by continuations is mapped. -/
def mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {A B : PFunctor.FreeM.Path spec → Type u} →
    (∀ tr, A tr → B tr) →
    StrategyOver (counterpartSyntax m) PUnit.unit spec roles A →
    StrategyOver (counterpartSyntax m) PUnit.unit spec roles B :=
  fun {spec} {roles} {A} {B} f =>
    ShapeOver.mapOutput
      (ShapeOver.TwoParty.PublicCoinCounterpart.counterpart (PFunctor.Lens.id Spec.basePFunctor) m)
      (agent := PUnit.unit) (spec := spec) roles
      (A := A) (B := B) f

/-- Forget the public-coin factorization and recover the ordinary executable
counterpart. -/
def toCounterpart {m : Type u → Type u} [Monad m] :
    {spec : Spec.{u}} → {roles : RoleDecoration spec} →
    {Output : PFunctor.FreeM.Path spec → Type u} →
    StrategyOver (counterpartSyntax m) PUnit.unit spec roles Output →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles Output
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
    {Output : PFunctor.FreeM.Path spec → Type u} →
    StrategyOver (counterpartSyntax m) PUnit.unit spec roles Output →
    (tr : PFunctor.FreeM.Path spec) → m (Output tr)
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
theorem _root_.Interaction.StrategyOver.TwoParty.Counterpart.mapOutput_id
    {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : PFunctor.FreeM.Path spec → Type u}
    (c : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles A) :
    StrategyOver.TwoParty.Counterpart.mapOutput (fun _ x => x) c = c := by
  match spec, roles with
  | .done, roles =>
      cases roles
      simp [StrategyOver.TwoParty.Counterpart.mapOutput, ShapeOver.mapOutput]
  | .node _ rest, ⟨.sender, rRest⟩ =>
      funext x
      have hid : ∀ c' : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
            (rest x) (rRest x) (fun p => A ⟨x, p⟩),
          StrategyOver.TwoParty.Counterpart.mapOutput
            (fun (p : PFunctor.FreeM.Path (rest x)) (y : A ⟨x, p⟩) => y) c' = c' :=
        fun c' =>
          @StrategyOver.TwoParty.Counterpart.mapOutput_id m _ _
            (rest x) (rRest x) (fun p => A ⟨x, p⟩) c'
      simp only [StrategyOver.TwoParty.Counterpart.mapOutput, ShapeOver.mapOutput,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired, PFunctor.Lens.id]
      change
        (StrategyOver.TwoParty.Counterpart.mapOutput
          (fun (p : PFunctor.FreeM.Path (rest x)) (y : A ⟨x, p⟩) => y)) <$> c x = c x
      calc (StrategyOver.TwoParty.Counterpart.mapOutput (fun p y => y) ·) <$> c x
          = id <$> c x := by congr 1; funext c'; exact hid c'
        _ = c x := LawfulFunctor.id_map (c x)
  | .node X rest, ⟨.receiver, rRest⟩ =>
      let F :
          ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) →
          ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
            (rest x) (rRest x) (fun p => A ⟨x, p⟩)) :=
        fun xc => ⟨xc.1,
          StrategyOver.TwoParty.Counterpart.mapOutput
            (fun (p : PFunctor.FreeM.Path (rest xc.1)) (y : A ⟨xc.1, p⟩) => y) xc.2⟩
      have hpair :
          F = id := by
        funext xc
        cases xc with
        | mk x c' =>
            simp only [F]
            have h :
                StrategyOver.TwoParty.Counterpart.mapOutput
                  (fun (p : PFunctor.FreeM.Path (rest x)) (y : A ⟨x, p⟩) => y) c' = c' := by
              simpa using
                (@StrategyOver.TwoParty.Counterpart.mapOutput_id m _ _
                  (rest x) (rRest x) (fun p => A ⟨x, p⟩) c')
            exact Sigma.ext rfl (heq_of_eq h)
      simp only [StrategyOver.TwoParty.Counterpart.mapOutput, ShapeOver.mapOutput,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired, PFunctor.Lens.id]
      change F <$> c = c
      rw [hpair]
      exact LawfulFunctor.id_map c

/-- Lift a deterministic counterpart into any monad.

At sender nodes the observational branch structure is unchanged. At receiver
nodes the chosen move and continuation are simply wrapped in `pure`. This is a
generic utility for reusing deterministic environments inside monadic execution
machinery built from `InteractionOver.run`. -/
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.liftId {m : Type u → Type u} [Monad m] :
    {spec : Spec} → {roles : RoleDecoration spec} →
    {Output : PFunctor.FreeM.Path spec → Type u} →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec Id) Participant.counterpart spec roles Output →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles Output
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
    {spec : Spec} (OutputP OutputC : PFunctor.FreeM.Path spec → Type u)
    (agent : Participant.{u}) (tr : PFunctor.FreeM.Path spec) : Type u :=
  match agent with
  | .focal => OutputP tr
  | .counterpart => OutputC tr

/-- Collect the two participant-indexed outputs into the result pair of a
two-party run. -/
def collectParticipantOutputs
    {spec : Spec} {OutputP OutputC : PFunctor.FreeM.Path spec → Type u} :
    (tr : PFunctor.FreeM.Path spec) →
      ((agent : Participant.{u}) → participantOutputFamily OutputP OutputC agent tr) →
      OutputP tr × OutputC tr :=
  fun _ out => (out Participant.focal, out Participant.counterpart)

/-- Assemble the focal strategy and counterpart strategy into a
participant-indexed profile for the generic runner. -/
def participantProfile
    {m : Type u → Type u} {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputC : PFunctor.FreeM.Path spec → Type u}
    (strat : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles OutputC) :
    (agent : Participant.{u}) →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) agent spec roles
        (participantOutputFamily OutputP OutputC agent)
  | .focal => strat
  | .counterpart => cpt

/-- Execute a focal/counterpart pair over a role-decorated interaction tree.

This is the generic `InteractionOver.run` specialized to `SyntaxOver.TwoParty.pairedSpec`, with the
two participant fibers assembled by `participantProfile` and collected by
`collectParticipantOutputs`.
-/
def run {m : Type u → Type u} [Monad m]
    (spec : Spec) (roles : RoleDecoration spec)
    {OutputP : PFunctor.FreeM.Path spec → Type u}
    {OutputC : PFunctor.FreeM.Path spec → Type u}
    (strat : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles OutputC) :
    m ((tr : PFunctor.FreeM.Path spec) × OutputP tr × OutputC tr) :=
  InteractionOver.runSpec
    (I := InteractionOver.TwoParty.pairedSpec m) roles (participantProfile strat cpt)
    collectParticipantOutputs

@[simp]
theorem _root_.Interaction.InteractionOver.TwoParty.run_paired_done {m : Type u → Type u} [Monad m]
    {OutputP OutputC : PFunctor.FreeM.Path Spec.done → Type u}
    (outP : OutputP ⟨⟩) (outC : OutputC ⟨⟩) :
    InteractionOver.runSpec
      (I := InteractionOver.TwoParty.pairedSpec m) (spec := Spec.done) (ctxs := PUnit.unit)
      (participantProfile outP outC) collectParticipantOutputs =
      (pure ⟨⟨⟩, outP, outC⟩ :
        m ((tr : PFunctor.FreeM.Path Spec.done) × OutputP tr × OutputC tr)) := by
  rfl

@[simp]
theorem _root_.Interaction.InteractionOver.TwoParty.run_paired_sender
    {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : PFunctor.FreeM.Path (Spec.node X rest) → Type u}
    (send :
      m ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
        (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualFn : (x : X) → m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    InteractionOver.runSpec
      (I := InteractionOver.TwoParty.pairedSpec m) (spec := Spec.node X rest)
      (ctxs := ⟨.sender, rRest⟩)
      (participantProfile
        (show StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
          (Spec.node X rest) ⟨.sender, rRest⟩ OutputP from send)
        (show StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
          (Spec.node X rest) ⟨.sender, rRest⟩ OutputC from dualFn))
      collectParticipantOutputs = (do
      let xc ← send
      let dualNext ← dualFn xc.1
      let tailOut ← InteractionOver.runSpec
        (I := InteractionOver.TwoParty.pairedSpec m) (spec := rest xc.1)
        (ctxs := rRest xc.1)
        (participantProfile xc.2 dualNext) collectParticipantOutputs
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simp only [InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
    SyntaxOver.TwoParty.pairedSpec, participantOutputFamily, participantProfile,
    collectParticipantOutputs]
  apply congrArg (fun k => send >>= k)
  funext xc
  apply congrArg (fun k => dualFn xc.1 >>= k)
  funext dualNext
  rfl

@[simp]
theorem _root_.Interaction.InteractionOver.TwoParty.run_paired_receiver
    {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : PFunctor.FreeM.Path (Spec.node X rest) → Type u}
    (respond : (x : X) → m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
      (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualSample :
      m ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
        (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    InteractionOver.runSpec
      (I := InteractionOver.TwoParty.pairedSpec m) (spec := Spec.node X rest)
      (ctxs := ⟨.receiver, rRest⟩)
      (participantProfile
        (show StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
          (Spec.node X rest) ⟨.receiver, rRest⟩ OutputP from respond)
        (show StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
          (Spec.node X rest) ⟨.receiver, rRest⟩ OutputC from dualSample))
      collectParticipantOutputs = (do
      let xc ← dualSample
      let next ← respond xc.1
      let tailOut ← InteractionOver.runSpec
        (I := InteractionOver.TwoParty.pairedSpec m) (spec := rest xc.1)
        (ctxs := rRest xc.1)
        (participantProfile next xc.2) collectParticipantOutputs
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simp only [InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
    SyntaxOver.TwoParty.pairedSpec, participantOutputFamily, participantProfile,
    collectParticipantOutputs]
  apply congrArg (fun k => dualSample >>= k)
  funext xc
  apply congrArg (fun k => respond xc.1 >>= k)
  funext next
  rfl

/-- Running a paired profile after mapping both participant outputs is the same
as running first and mapping the final triple. -/
theorem _root_.Interaction.InteractionOver.TwoParty.run_paired_mapOutput_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputP' OutputC OutputC' : PFunctor.FreeM.Path spec → Type u}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles OutputC) :
    InteractionOver.runSpec
      (I := InteractionOver.TwoParty.pairedSpec m) (spec := spec) (ctxs := roles)
      (participantProfile
        (StrategyOver.TwoParty.Focal.mapOutput fP strat)
        (StrategyOver.TwoParty.Counterpart.mapOutput fC cpt))
      collectParticipantOutputs =
      (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
        InteractionOver.runSpec
          (I := InteractionOver.TwoParty.pairedSpec m) (spec := spec) (ctxs := roles)
          (participantProfile strat cpt) collectParticipantOutputs := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec)
      {OutputP OutputP' OutputC OutputC' : PFunctor.FreeM.Path spec → Type u}
      (fP : ∀ tr, OutputP tr → OutputP' tr)
      (fC : ∀ tr, OutputC tr → OutputC' tr)
      (strat : StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles OutputP)
      (cpt : StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles OutputC) :
      InteractionOver.runSpec
        (I := InteractionOver.TwoParty.pairedSpec m) (spec := spec) (ctxs := roles)
        (participantProfile
        (StrategyOver.TwoParty.Focal.mapOutput fP strat)
        (StrategyOver.TwoParty.Counterpart.mapOutput fC cpt))
        collectParticipantOutputs =
        (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
          InteractionOver.runSpec
            (I := InteractionOver.TwoParty.pairedSpec m) (spec := spec) (ctxs := roles)
            (participantProfile strat cpt) collectParticipantOutputs := by
    match spec, roles with
    | .done, roles =>
        cases roles
        simp [StrategyOver.TwoParty.Focal.mapOutput,
          StrategyOver.TwoParty.Counterpart.mapOutput, ShapeOver.mapOutput,
          InteractionOver.runSpec,
          participantProfile, collectParticipantOutputs]
    | .node X rest, ⟨.sender, rRest⟩ =>
        simp only [StrategyOver.TwoParty.Focal.mapOutput,
          StrategyOver.TwoParty.Counterpart.mapOutput]
        simp only [InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired, SyntaxOver.TwoParty.pairedSpec, participantOutputFamily,
          participantProfile, collectParticipantOutputs, bind_pure_comp]
        refine (bind_map_left
          (fun xc =>
            (⟨xc.1, StrategyOver.TwoParty.Focal.mapOutput (fun p => fP ⟨xc.1, p⟩) xc.2⟩ :
              (x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
                (rest x) (rRest x) (fun tr => OutputP' ⟨x, tr⟩)))
          strat _).trans ?_
        simp only [map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext xc
        refine (bind_map_left
          (fun cNext => StrategyOver.TwoParty.Counterpart.mapOutput (fun p => fC ⟨xc.1, p⟩) cNext)
          (cpt xc.1) _).trans ?_
        refine congrArg (fun k => cpt xc.1 >>= k) ?_
        funext cNext
        let addPrefix :
            ((tr : PFunctor.FreeM.Path (rest xc.1)) × (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : PFunctor.FreeM.Path (Spec.node _ rest)) × OutputP' tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [monad_norm, addPrefix, PFunctor.Lens.id, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (fun tr => fP ⟨xc.1, tr⟩) (fun tr => fC ⟨xc.1, tr⟩)
              xc.2 cNext)
    | .node X rest, ⟨.receiver, rRest⟩ =>
        simp only [StrategyOver.TwoParty.Focal.mapOutput,
          StrategyOver.TwoParty.Counterpart.mapOutput]
        simp only [InteractionOver.runSpec, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired, SyntaxOver.TwoParty.pairedSpec, participantOutputFamily,
          participantProfile, collectParticipantOutputs, bind_pure_comp]
        refine (bind_map_left
          (fun xc =>
            (⟨xc.1, StrategyOver.TwoParty.Counterpart.mapOutput (fun p => fC ⟨xc.1, p⟩) xc.2⟩ :
              (x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
                (rest x) (rRest x) (fun tr => OutputC' ⟨x, tr⟩)))
          cpt _).trans ?_
        simp only [map_bind, Functor.map_map]
        refine congrArg (fun k => cpt >>= k) ?_
        funext xc
        refine (bind_map_left
          (fun next => StrategyOver.TwoParty.Focal.mapOutput (fun p => fP ⟨xc.1, p⟩) next)
          (strat xc.1) _).trans ?_
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : PFunctor.FreeM.Path (rest xc.1)) × (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : PFunctor.FreeM.Path (Spec.node _ rest)) × OutputP' tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [monad_norm, addPrefix, PFunctor.Lens.id, InteractionOver.TwoParty.pairedSpec,
          InteractionOver.TwoParty.paired] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (fun tr => fP ⟨xc.1, tr⟩) (fun tr => fC ⟨xc.1, tr⟩)
              next xc.2)
  exact go spec roles fP fC strat cpt

@[simp]
theorem run_done {m : Type u → Type u} [Monad m]
    {OutputP OutputC : PFunctor.FreeM.Path Spec.done → Type u}
    (outP : OutputP ⟨⟩) (outC : OutputC ⟨⟩) :
    run .done PUnit.unit outP outC =
      (pure ⟨⟨⟩, outP, outC⟩ :
        m ((tr : PFunctor.FreeM.Path Spec.done) × OutputP tr × OutputC tr)) := by
  rfl

@[simp]
theorem run_sender {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : PFunctor.FreeM.Path (Spec.node X rest) → Type u}
    (send :
      m ((x : X) × StrategyOver
        (SyntaxOver.TwoParty.pairedSpec m) Participant.focal (rest x) (rRest x)
        (fun tr => OutputP ⟨x, tr⟩)))
    (dualFn : (x : X) → m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    run (Spec.node X rest) ⟨.sender, rRest⟩ send dualFn = (do
      let xc ← send
      let dualNext ← dualFn xc.1
      let tailOut ← run (rest xc.1) (rRest xc.1) xc.2 dualNext
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simpa [run] using InteractionOver.TwoParty.run_paired_sender send dualFn

@[simp]
theorem run_receiver {m : Type u → Type u} [Monad m]
    {X : Type u} {rest : X → Spec} {rRest : (x : X) → RoleDecoration (rest x)}
    {OutputP OutputC : PFunctor.FreeM.Path (Spec.node X rest) → Type u}
    (respond : (x : X) → m (StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
      (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩)))
    (dualSample :
      m ((x : X) × StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
        (rest x) (rRest x) (fun tr => OutputC ⟨x, tr⟩))) :
    run (Spec.node X rest) ⟨.receiver, rRest⟩ respond dualSample = (do
      let xc ← dualSample
      let next ← respond xc.1
      let tailOut ← run (rest xc.1) (rRest xc.1) next xc.2
      pure ⟨⟨xc.1, tailOut.1⟩, tailOut.2⟩) := by
  simpa [run] using InteractionOver.TwoParty.run_paired_receiver respond dualSample

theorem run_mapOutput_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputP' OutputC OutputC' : PFunctor.FreeM.Path spec → Type u}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles OutputP)
    (cpt : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles OutputC) :
    run spec roles (StrategyOver.TwoParty.Focal.mapOutput fP strat)
      (StrategyOver.TwoParty.Counterpart.mapOutput fC cpt) =
      (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
        run spec roles strat cpt := by
  simpa [run] using
    (InteractionOver.TwoParty.run_paired_mapOutput_mapOutput (m := m)
      fP fC strat cpt)

/--
View a strategy over a constant monad decoration as an ordinary single-monad
role strategy.
-/
def _root_.Interaction.StrategyOver.TwoParty.Focal.ofConstantMonads {m : Type u → Type u} [Monad m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output : PFunctor.FreeM.Path spec → Type u} :
    StrategyOver SyntaxOver.TwoParty.Focal.monadicSpec PUnit.unit spec
      (RoleDecoration.withMonads roles (Spec.MonadDecoration.constant ⟨m, inferInstance⟩ spec))
      Output →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles Output :=
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
def _root_.Interaction.StrategyOver.TwoParty.Focal.toConstantMonadsHom
    {m : Type u → Type u} [Monad m] [LawfulFunctor m] :
    StrategyOver.ShapeContextHom
      (ShapeOver.TwoParty.pairedSpec m) (Participant.focal : Participant.{u})
      ShapeOver.TwoParty.Focal.monadicSpec PUnit.unit
      (RoleContext.withMonad ⟨m, inferInstance⟩) where
  mapNode := by
    intro X role A B f node
    cases role
    · simpa [ShapeOver.TwoParty.Focal.monadicSpec, SyntaxOver.TwoParty.Focal.monadicSpec,
        ShapeOver.comap, SyntaxOver.comap, ShapeOver.forAgent, SyntaxOver.forAgent,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
        SyntaxOver.TwoParty.pairedSpec, SyntaxOver.TwoParty.paired,
        ShapeOver.TwoParty.pairedMonadicSpec, ShapeOver.TwoParty.pairedMonadic,
        SyntaxOver.TwoParty.pairedMonadicSpec, SyntaxOver.TwoParty.pairedMonadic]
        using (ShapeOver.TwoParty.pairedSpec m).map
          (agent := Participant.focal) (γ := Role.sender) f node
    · simpa [ShapeOver.TwoParty.Focal.monadicSpec, SyntaxOver.TwoParty.Focal.monadicSpec,
        ShapeOver.comap, SyntaxOver.comap, ShapeOver.forAgent, SyntaxOver.forAgent,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
        SyntaxOver.TwoParty.pairedSpec, SyntaxOver.TwoParty.paired,
        ShapeOver.TwoParty.pairedMonadicSpec, ShapeOver.TwoParty.pairedMonadic,
        SyntaxOver.TwoParty.pairedMonadicSpec, SyntaxOver.TwoParty.pairedMonadic]
        using (ShapeOver.TwoParty.pairedSpec m).map
          (agent := Participant.focal) (γ := Role.receiver) f node
  mapNode_map := by
    intro X role A B C D f₁ f₂ g₁ g₂ comm node
    cases role
    · have hfun :
          (fun dx : (d : (PFunctor.Lens.id Spec.basePFunctor).toFunA X) × A d =>
            Sigma.mk dx.1 (g₁ dx.1 (f₁ dx.1 dx.2))) =
          (fun dx : (d : (PFunctor.Lens.id Spec.basePFunctor).toFunA X) × A d =>
            Sigma.mk dx.1 (g₂ dx.1 (f₂ dx.1 dx.2))) := by
          funext dx
          exact Sigma.ext rfl (heq_of_eq (comm dx.1 dx.2))
      simpa [ShapeOver.TwoParty.Focal.monadicSpec, SyntaxOver.TwoParty.Focal.monadicSpec,
        ShapeOver.comap, SyntaxOver.comap, ShapeOver.forAgent, SyntaxOver.forAgent,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
        SyntaxOver.TwoParty.pairedSpec, SyntaxOver.TwoParty.paired,
        RoleMonadContext.diagonal, Spec.Node.Context.extendMap, Spec.Node.ContextHom.id,
        ShapeOver.TwoParty.pairedMonadicSpec, ShapeOver.TwoParty.pairedMonadic,
        SyntaxOver.TwoParty.pairedMonadicSpec, SyntaxOver.TwoParty.pairedMonadic,
        Functor.map_map]
        using congrArg (fun h => h <$> node) hfun
    · funext x
      have hfun : (fun y : A x => g₁ x (f₁ x y)) = (fun y : A x => g₂ x (f₂ x y)) := by
        funext y
        exact comm x y
      simpa [ShapeOver.TwoParty.Focal.monadicSpec, SyntaxOver.TwoParty.Focal.monadicSpec,
        ShapeOver.comap, SyntaxOver.comap, ShapeOver.forAgent, SyntaxOver.forAgent,
        ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
        SyntaxOver.TwoParty.pairedSpec, SyntaxOver.TwoParty.paired,
        RoleMonadContext.diagonal, Spec.Node.Context.extendMap, Spec.Node.ContextHom.id,
        ShapeOver.TwoParty.pairedMonadicSpec, ShapeOver.TwoParty.pairedMonadic,
        SyntaxOver.TwoParty.pairedMonadicSpec, SyntaxOver.TwoParty.pairedMonadic,
        Functor.map_map]
        using congrArg (fun h => h <$> node x) hfun

/--
View an ordinary single-monad role strategy as a monadic focal strategy by
structurally pairing every role label with the same bundled monad.
-/
def _root_.Interaction.StrategyOver.TwoParty.Focal.toConstantMonads
    {m : Type u → Type u} [Monad m] [LawfulFunctor m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output : PFunctor.FreeM.Path spec → Type u} :
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles Output →
    StrategyOver ShapeOver.TwoParty.Focal.monadicSpec.toSyntaxOver PUnit.unit spec
      (Decoration.map (RoleContext.withMonad ⟨m, inferInstance⟩) spec roles)
      Output :=
  StrategyOver.mapContext
    StrategyOver.TwoParty.Focal.toConstantMonadsHom.toContextHom
    (spec := spec) (ctxs := roles)

/--
Lifting an ordinary role strategy into a constant monad decoration commutes
with output maps.

This is the naturality property used at boundaries that still accept ordinary
single-monad strategies while internal execution is phrased over nodewise
monad decorations.
-/
theorem _root_.Interaction.StrategyOver.TwoParty.Focal.toConstantMonads_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulFunctor m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output Output' : PFunctor.FreeM.Path spec → Type u}
    (f : ∀ tr, Output tr → Output' tr)
    (strat : StrategyOver
      (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles Output) :
    StrategyOver.TwoParty.Focal.toConstantMonads spec roles
        (StrategyOver.TwoParty.Focal.mapOutput f strat) =
      ShapeOver.mapOutput ShapeOver.TwoParty.Focal.monadicSpec
        (agent := PUnit.unit)
        (spec := spec)
        (ctxs := Decoration.map (RoleContext.withMonad ⟨m, inferInstance⟩) spec roles)
        f
        (StrategyOver.TwoParty.Focal.toConstantMonads spec roles strat) :=
  StrategyOver.mapContext_mapOutput StrategyOver.TwoParty.Focal.toConstantMonadsHom
    (ctxs := roles) f strat

/--
Retarget a monadic focal strategy along a nodewise monad homomorphism.

This traverses the strategy tree structurally, applying the supplied lift at
each node and recursing through the selected continuation.
-/
def _root_.Interaction.StrategyOver.TwoParty.Focal.mapMonadDecoration
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {md₁ md₂ : Spec.MonadDecoration spec}
    (hom : Spec.MonadDecoration.Hom spec md₁ md₂)
    {Output : PFunctor.FreeM.Path spec → Type u} :
    StrategyOver SyntaxOver.TwoParty.Focal.monadicSpec PUnit.unit spec
      (RoleDecoration.withMonads roles md₁) Output →
    StrategyOver SyntaxOver.TwoParty.Focal.monadicSpec PUnit.unit spec
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
def _root_.Interaction.StrategyOver.TwoParty.Counterpart.mapMonadDecoration
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {md₁ md₂ : Spec.MonadDecoration spec}
    (hom : Spec.MonadDecoration.Hom spec md₁ md₂)
    {Output : PFunctor.FreeM.Path spec → Type u} :
    StrategyOver SyntaxOver.TwoParty.Counterpart.monadicSpec PUnit.unit spec
      (RoleDecoration.withMonads roles md₁) Output →
    StrategyOver SyntaxOver.TwoParty.Counterpart.monadicSpec PUnit.unit spec
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
def _root_.Interaction.InteractionOver.TwoParty.pairedMonadicSpec {m : Type u → Type u} [Monad m]
    (liftStrat : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α)
    (liftCpt : ∀ (bm : BundledMonad.{u, u}) {α : Type u}, bm.M α → m α) :
    InteractionOver
      (PFunctor.Lens.id Spec.basePFunctor) Participant.{u} RolePairedMonadContext
      SyntaxOver.TwoParty.pairedMonadicSpec m :=
  InteractionOver.TwoParty.pairedMonadic
    (PFunctor.Lens.id Spec.basePFunctor) liftStrat liftCpt

end TwoParty
end Interaction
