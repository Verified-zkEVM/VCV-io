/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Multiparty.Broadcast
import VCVio.Interaction.Multiparty.Directed
import VCVio.Interaction.Multiparty.Profile

/-!
# Examples: multiparty endpoints with local views

This file contains examples showing how the native multiparty endpoint types
compute definitionally in the broadcast, directed, and profile-based
communication models introduced in the new `Interaction.Multiparty` layer.

Besides the basic broadcast and directed examples, the later sections focus on
adversarial semantics. They show that the current sequential `Interaction.Spec`
framework can already model, in a definitionally transparent way:
* public-transcript adversarial choices;
* directed delivery with hidden outsiders;
* metadata leakage without full payload leakage;
* adversarial choices among dropping, delivering, and duplicating messages; and
* adaptive adversarial power where earlier choices change later local views.

The examples are written using pattern-matching resolvers rather than equality
tests. This is deliberate: for concrete finite party types, it keeps the local
endpoint types definitionally transparent.
-/

universe u

namespace Interaction
namespace Multiparty

section BroadcastExamples

inductive ThreeParty : Type u where
  | prover
  | verifier
  | extractor
  deriving DecidableEq

namespace ThreeParty

/--
`resolveBroadcastFor me owner` is the local-view projection of the broadcast
model to the fixed participant `me`.

At nodes owned by `me`, the result is `LocalView.active`.
At all other nodes, the result is `LocalView.observe`.

This definition is written by pattern matching, rather than by equality tests,
so that endpoint types reduce definitionally in examples.
-/
def resolveBroadcastFor (me owner : ThreeParty) {X : Type u} : LocalView X :=
      match me, owner with
      | .prover, .prover => .active
      | .prover, .verifier => .observe
      | .prover, .extractor => .observe
      | .verifier, .prover => .observe
      | .verifier, .verifier => .active
      | .verifier, .extractor => .observe
      | .extractor, .prover => .observe
      | .extractor, .verifier => .observe
      | .extractor, .extractor => .active

/--
`resolveDirectedFor me src dst` is the local-view projection of the directed
model to the fixed participant `me`.

It returns:
* `active` when `me` is the node's source party;
* `observe` when `me` is the node's designated destination party;
* `hidden` otherwise.

As in the broadcast model, this resolver is defined by pattern matching, so
that local endpoint types unfold definitionally.
-/
def resolveDirectedFor (me src dst : ThreeParty) {X : Type u} : LocalView X :=
      match me, src, dst with
      | .prover, .prover, _ => .active
      | .prover, _, .prover => .observe
      | .prover, _, _ => .hidden
      | .verifier, .verifier, _ => .active
      | .verifier, _, .verifier => .observe
      | .verifier, _, _ => .hidden
      | .extractor, .extractor, _ => .active
      | .extractor, _, .extractor => .observe
      | .extractor, _, _ => .hidden

end ThreeParty

section KnowledgeSoundnessBroadcast

variable (Msg Chal WitOut : Type u)
variable (Decision : Type u)
variable (ExtractedWit : Type u)

/-- Spec for a one-round knowledge-soundness interaction:
message, challenge, witness output, decision, extraction. -/
private def ksSpec : Spec :=
  Spec.node Msg fun _ => .node Chal fun _ => .node WitOut fun _ =>
  .node Decision fun _ => .node ExtractedWit fun _ => .done

/-- Acting parties for the knowledge-soundness interaction in the broadcast
model. -/
private def ksParties :
    Broadcast.PartyDecoration ThreeParty
      (ksSpec Msg Chal WitOut Decision ExtractedWit) :=
  ⟨.prover, fun _ => ⟨.verifier, fun _ => ⟨.prover, fun _ =>
    ⟨.verifier, fun _ => ⟨.extractor, fun _ => ⟨⟩⟩⟩⟩⟩⟩

variable (m : Type u → Type u) [Monad m] (α : Type u)

/-- Prover endpoint in the broadcast model:
choose msg, observe chal, choose witness, observe decision, observe extraction. -/
example :
    Broadcast.Strategy (Party := ThreeParty) m (ksSpec Msg Chal WitOut Decision ExtractedWit)
      (ksParties Msg Chal WitOut Decision ExtractedWit)
      (fun {_} (owner : ThreeParty) => ThreeParty.resolveBroadcastFor ThreeParty.prover owner)
      (fun _ => α)
    = m ((_ : Msg) × ((_ : Chal) → m (m ((_ : WitOut) ×
        ((_ : Decision) → m ((_ : ExtractedWit) → m α)))))) := rfl

/-- Verifier endpoint in the broadcast model:
observe msg, choose chal, observe witness, choose decision, observe extraction. -/
example :
    Broadcast.Strategy (Party := ThreeParty) m (ksSpec Msg Chal WitOut Decision ExtractedWit)
      (ksParties Msg Chal WitOut Decision ExtractedWit)
      (fun {_} (owner : ThreeParty) => ThreeParty.resolveBroadcastFor ThreeParty.verifier owner)
      (fun _ => α)
    = ((_ : Msg) → m (m ((_ : Chal) × ((_ : WitOut) → m
        (m ((_ : Decision) × ((_ : ExtractedWit) → m α))))))) := rfl

/-- Extractor endpoint in the broadcast model:
observe every earlier move, then choose the extraction output. -/
example :
    Broadcast.Strategy (Party := ThreeParty) m (ksSpec Msg Chal WitOut Decision ExtractedWit)
      (ksParties Msg Chal WitOut Decision ExtractedWit)
      (fun {_} (owner : ThreeParty) => ThreeParty.resolveBroadcastFor ThreeParty.extractor owner)
      (fun _ => α)
    = ((_ : Msg) → m ((_ : Chal) → m ((_ : WitOut) → m
        ((_ : Decision) → m (m ((_ : ExtractedWit) × α)))))) := rfl

end KnowledgeSoundnessBroadcast

end BroadcastExamples

section DirectedExamples

variable (Msg Ack : Type u)
variable (m : Type u → Type u) [Monad m] (α : Type u)

/-- A tiny two-step protocol used to demonstrate the directed model:
`prover → verifier`, then `verifier → extractor`. -/
private def directedSpec : Spec :=
  Spec.node Msg fun _ => .node Ack fun _ => .done

/-- Directed sender/receiver labels for `directedSpec`. -/
private def directedEdges :
    Directed.EdgeDecoration ThreeParty (directedSpec Msg Ack) :=
  ⟨(.prover, .verifier), fun _ => ⟨(.verifier, .extractor), fun _ => ⟨⟩⟩⟩

/-- Prover endpoint in the directed model:
send the first move, then become hidden in the second. -/
example :
    Directed.Strategy (Party := ThreeParty) m (directedSpec Msg Ack) (directedEdges Msg Ack)
      (fun {_} (src dst : ThreeParty) => ThreeParty.resolveDirectedFor ThreeParty.prover src dst)
      (fun _ => α)
    = m ((_ : Msg) × m ((_ : Ack) → α)) := rfl

/-- Verifier endpoint in the directed model:
observe the first move, then send the second. -/
example :
    Directed.Strategy (Party := ThreeParty) m (directedSpec Msg Ack) (directedEdges Msg Ack)
      (fun {_} (src dst : ThreeParty) => ThreeParty.resolveDirectedFor ThreeParty.verifier src dst)
      (fun _ => α)
    = ((_ : Msg) → m (m ((_ : Ack) × α))) := rfl

/-- Extractor endpoint in the directed model:
be hidden in the first move, then observe the second. -/
example :
    Directed.Strategy (Party := ThreeParty) m (directedSpec Msg Ack) (directedEdges Msg Ack)
      (fun {_} (src dst : ThreeParty) => ThreeParty.resolveDirectedFor ThreeParty.extractor src dst)
      (fun _ => α)
    = m ((_ : Msg) → ((_ : Ack) → m α)) := rfl

end DirectedExamples

section PartialObservationExamples

inductive ScheduleParty : Type u where
  | adversary
  | recipient
  | auditor
  | outsider
  deriving DecidableEq

variable (Msg : Type u)
variable (Flag : Type u)
variable (m : Type u → Type u) [Monad m] (α : Type u)

/-- A one-step scheduled event with a public tag and a private payload. -/
private def scheduledSpec : Spec :=
  Spec.node (Flag × Msg) fun _ => .done

/-- Per-party local views of the scheduled event:
the adversary chooses, the recipient observes the full event, the auditor
learns only the public tag, and the outsider learns nothing. -/
private def scheduledViews :
    Profile.Decoration ScheduleParty (scheduledSpec Msg Flag) :=
  ⟨(fun
      | .adversary => .active
      | .recipient => .observe
      | .auditor => .quotient Flag Prod.fst
      | .outsider => .hidden), fun _ => ⟨⟩⟩

/-- The adversary chooses the full scheduled event. -/
example :
    Profile.Strategy (Party := ScheduleParty) m ScheduleParty.adversary
      (scheduledSpec Msg Flag) (scheduledViews Msg Flag) (fun _ => α)
    = m ((_ : Flag × Msg) × α) := rfl

/-- The recipient is told the full event. -/
example :
    Profile.Strategy (Party := ScheduleParty) m ScheduleParty.recipient
      (scheduledSpec Msg Flag) (scheduledViews Msg Flag) (fun _ => α)
    = ((x : Flag × Msg) → m α) := rfl

/-- The auditor learns only the public scheduling bit. -/
example :
    Profile.Strategy (Party := ScheduleParty) m ScheduleParty.auditor
      (scheduledSpec Msg Flag) (scheduledViews Msg Flag) (fun _ => α)
    = ((o : Flag) → m ((x : Flag × Msg) → Prod.fst x = o → α)) := rfl

/-- The outsider learns nothing about which event actually occurred. -/
example :
    Profile.Strategy (Party := ScheduleParty) m ScheduleParty.outsider
      (scheduledSpec Msg Flag) (scheduledViews Msg Flag) (fun _ => α)
    = m ((_ : Flag × Msg) → α) := rfl

end PartialObservationExamples

section ConditionalDeliveryExamples

/--
`DeliveryParty` is a small network with one active adversary, two possible
recipients, one auditor, and one completely uninformed outsider.
-/
inductive DeliveryParty : Type u where
  | adversary
  | bob
  | carol
  | auditor
  | outsider
  deriving DecidableEq

/--
The public scheduling summary of a network action.

This forgets message payloads and records only who, if anyone, received a
delivery.
-/
inductive DeliverySummary : Type u where
  | none
  | bob
  | carol
  | both
  deriving DecidableEq

/--
Possible one-step powers of a scheduling adversary for a single pending
message.

The adversary may:
* drop the message entirely;
* deliver it only to Bob;
* deliver it only to Carol; or
* duplicate it and deliver to both Bob and Carol.
-/
inductive NetworkAction (Msg : Type u) : Type u where
  | drop
  | deliverBob (msg : Msg)
  | deliverCarol (msg : Msg)
  | duplicate (msg : Msg)
  deriving DecidableEq

variable (Msg : Type u)
variable (m : Type u → Type u) [Monad m] (α : Type u)

/--
Bob's local observation of a network action.

Bob learns the payload exactly in the branches where Bob receives a delivery,
and otherwise learns only that no payload was received by Bob.
-/
private def bobObservation : NetworkAction Msg → Option Msg
  | .drop => none
  | .deliverBob msg => some msg
  | .deliverCarol _ => none
  | .duplicate msg => some msg

/--
Carol's local observation of a network action.

This is dual to Bob's observation.
-/
private def carolObservation : NetworkAction Msg → Option Msg
  | .drop => none
  | .deliverBob _ => none
  | .deliverCarol msg => some msg
  | .duplicate msg => some msg

/--
The public scheduling summary seen by an external auditor.

The auditor learns which delivery pattern occurred, but never learns the
payload.
-/
private def deliverySummary : NetworkAction Msg → DeliverySummary
  | .drop => .none
  | .deliverBob _ => .bob
  | .deliverCarol _ => .carol
  | .duplicate _ => .both

/--
A one-step adversarially scheduled delivery action.
-/
private def networkSpec : Spec :=
  Spec.node (NetworkAction Msg) fun _ => .done

/--
Per-party views of `networkSpec`.

This single node already captures several adversarial powers:
* the adversary chooses the actual network action;
* Bob and Carol each learn only the payloads they themselves receive;
* the auditor learns only the public delivery pattern; and
* the outsider learns nothing at all.
-/
private def networkViews :
    Profile.Decoration DeliveryParty (networkSpec Msg) :=
  ⟨(fun
      | .adversary => .active
      | .bob => .quotient (Option Msg) (bobObservation (Msg := Msg))
      | .carol => .quotient (Option Msg) (carolObservation (Msg := Msg))
      | .auditor => .quotient DeliverySummary (deliverySummary (Msg := Msg))
      | .outsider => .hidden), fun _ => ⟨⟩⟩

/-- The adversary chooses the exact network action. -/
example :
    Profile.Strategy (Party := DeliveryParty) m DeliveryParty.adversary
      (networkSpec Msg) (networkViews Msg) (fun _ => α)
    = m ((_ : NetworkAction Msg) × α) := rfl

/--
Bob learns exactly the payload, if any, that Bob receives.

This one quotient node simultaneously covers dropping, Bob-only delivery,
Carol-only delivery, and duplication.
-/
example :
    Profile.Strategy (Party := DeliveryParty) m DeliveryParty.bob
      (networkSpec Msg) (networkViews Msg) (fun _ => α)
    = ((o : Option Msg) →
        m ((x : NetworkAction Msg) → bobObservation (Msg := Msg) x = o → α)) := rfl

/-- Carol's endpoint is the symmetric quotient-observation endpoint. -/
example :
    Profile.Strategy (Party := DeliveryParty) m DeliveryParty.carol
      (networkSpec Msg) (networkViews Msg) (fun _ => α)
    = ((o : Option Msg) →
        m ((x : NetworkAction Msg) → carolObservation (Msg := Msg) x = o → α)) := rfl

/-- The auditor sees only the public delivery pattern and never the payload. -/
example :
    Profile.Strategy (Party := DeliveryParty) m DeliveryParty.auditor
      (networkSpec Msg) (networkViews Msg) (fun _ => α)
    = ((s : DeliverySummary) →
        m ((x : NetworkAction Msg) → deliverySummary (Msg := Msg) x = s → α)) := rfl

/-- The outsider learns nothing about which network action actually occurred. -/
example :
    Profile.Strategy (Party := DeliveryParty) m DeliveryParty.outsider
      (networkSpec Msg) (networkViews Msg) (fun _ => α)
    = m ((_ : NetworkAction Msg) → α) := rfl

end ConditionalDeliveryExamples

section AdaptiveCorruptionExamples

/--
Parties in a tiny adaptive-corruption example.

The adversary first chooses whom to corrupt, and then gains active control over
the next move that emerges from the corrupted side.
-/
inductive CorruptionParty : Type u where
  | adversary
  | alice
  | bob
  | monitor
  deriving DecidableEq

/-- The honest party corrupted by the adversary. -/
inductive CorruptionTarget : Type u where
  | alice
  | bob
  deriving DecidableEq

variable (Secret : Type u)
variable (m : Type u → Type u) [Monad m] (α : Type u)

/--
A bounded adaptive-corruption protocol.

The first move is the adversary's corruption decision. The second move is a
post-corruption secret-bearing action whose local visibility depends on the
chosen corruption target.
-/
private def corruptionSpec : Spec :=
  Spec.node CorruptionTarget fun _ => .node Secret fun _ => .done

/--
Per-party local views for `corruptionSpec`.

At the root, the corruption target is public. Afterwards:
* the adversary actively controls the corrupted side's next move;
* the corrupted party observes that move;
* the uncorrupted party is hidden from it; and
* the external monitor learns only the public corruption decision.

This exhibits a key adversarial feature of the framework:
the local views at later nodes can depend definitionally on earlier
adversarially chosen moves.
-/
private def corruptionViews :
    Profile.Decoration CorruptionParty (corruptionSpec Secret) :=
  ⟨(fun
      | .adversary => .active
      | .alice => .observe
      | .bob => .observe
      | .monitor => .observe), fun
      | .alice =>
          ⟨(fun
              | .adversary => .active
              | .alice => .observe
              | .bob => .hidden
              | .monitor => .hidden), fun _ => ⟨⟩⟩
      | .bob =>
          ⟨(fun
              | .adversary => .active
              | .alice => .hidden
              | .bob => .observe
              | .monitor => .hidden), fun _ => ⟨⟩⟩⟩

/--
`corruptionAdversaryViews` is the local-view projection of `corruptionViews`
to the adversary.

It is written explicitly so that the resulting endpoint computation reduces by
`rfl`.
-/
private def corruptionAdversaryViews :
    Spec.Decoration (fun X : Type u => LocalView X) (corruptionSpec Secret) :=
  ⟨.active, fun _ => ⟨.active, fun _ => ⟨⟩⟩⟩

/--
`corruptionMonitorViews` is the local-view projection of `corruptionViews`
to the external monitor.

The monitor learns the public corruption decision but is hidden from the later
secret-bearing move in every branch.
-/
private def corruptionMonitorViews :
    Spec.Decoration (fun X : Type u => LocalView X) (corruptionSpec Secret) :=
  ⟨.observe, fun _ => ⟨.hidden, fun _ => ⟨⟩⟩⟩

/--
The post-corruption secret-bearing node viewed from the branch where Alice is
the corrupted party.
-/
private def aliceAfterSelfCorruptionViews :
    Spec.Decoration (fun X : Type u => LocalView X) (Spec.node Secret fun _ => .done) :=
  ⟨.observe, fun _ => ⟨⟩⟩

/--
The same post-corruption secret-bearing node viewed from the branch where Bob
is corrupted instead, so Alice is hidden from the move.
-/
private def aliceAfterBobCorruptionViews :
    Spec.Decoration (fun X : Type u => LocalView X) (Spec.node Secret fun _ => .done) :=
  ⟨.hidden, fun _ => ⟨⟩⟩

/--
The adversary chooses whom to corrupt and then actively controls the next
secret-bearing move in that branch.
-/
example :
    Multiparty.Strategy m (resolve := fun _ view => view)
      (corruptionSpec Secret) (corruptionAdversaryViews Secret) (fun _ => α)
    = m ((_ : CorruptionTarget) × m ((_ : Secret) × α)) := rfl

/--
Alice first observes the public corruption decision.

After that, the second-step local view depends on the chosen branch.
The two examples below exhibit the two branch-local endpoint shapes that the
adversary's first move can induce for Alice.
-/
example :
    Multiparty.Strategy m
      (resolve := Spec.Node.ContextHom.id (fun X : Type u => LocalView X))
      (Spec.node Secret fun _ => .done) (aliceAfterSelfCorruptionViews Secret)
      (fun _ => α)
    = ((_ : Secret) → m α) := by
  unfold Multiparty.Strategy
  rw [Spec.SyntaxOver.comap_id]
  rfl

/--
If Bob is corrupted instead, Alice is hidden from the same second-step node.
-/
example :
    Multiparty.Strategy m
      (resolve := Spec.Node.ContextHom.id (fun X : Type u => LocalView X))
      (Spec.node Secret fun _ => .done) (aliceAfterBobCorruptionViews Secret)
      (fun _ => α)
    = m ((_ : Secret) → α) := by
  unfold Multiparty.Strategy
  rw [Spec.SyntaxOver.comap_id]
  rfl

/--
The monitor learns the public corruption decision but is hidden from the later
secret-bearing move regardless of the branch.
-/
example :
    Multiparty.Strategy m (resolve := fun _ view => view)
      (corruptionSpec Secret) (corruptionMonitorViews Secret) (fun _ => α)
    = ((target : CorruptionTarget) → m (m ((_ : Secret) → α))) := rfl

end AdaptiveCorruptionExamples

end Multiparty
end Interaction
