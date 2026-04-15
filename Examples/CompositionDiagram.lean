/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.Notation
import VCVioWidgets.OpenSyntax.Render
import VCVioWidgets.OpenSyntax.Panel
import VCVioWidgets.OpenSyntax.TreePanel

/-!
# Diffie-Hellman key exchange as a composition diagram

Demonstrates the `@[show_composition]` panel widget and `Raw.toDot` DOT
renderer on a real cryptographic example: Diffie-Hellman (DH) key exchange
in the UC paradigm.

The UC paradigm decomposes a protocol into two compositions:

* **Real world**: concrete protocol parties (Alice, Bob) communicate over an
  insecure channel, with the whole system closed against an adversarial
  environment.
* **Ideal world**: an ideal key-exchange functionality plus a simulator
  communicate over a dummy channel, closed against the same environment.

UC security states that no environment can distinguish between the two.

Two layout variants are shown in the infoview for comparison:
* Force-directed graph (draggable, D3)
* Computed tree layout (static SVG)

Use `Raw.toDot` to export Graphviz DOT strings for external rendering.
-/

show_panel_widgets [
  local VCVioWidgets.OpenSyntax.CompositionPanel,
  local VCVioWidgets.OpenSyntax.TreePanel]

open Interaction.UC
open Interaction.UC.OpenSyntax

-- Symmetric boundary where In = Out, so `swap bd = bd` definitionally.
private abbrev bd : PortBoundary :=
  ⟨⟨Unit, fun _ => Unit⟩, ⟨Unit, fun _ => Unit⟩⟩

private abbrev bd2 : PortBoundary := bd ⊗ᵇ bd

/--
Protocol components for a DH key exchange in the UC paradigm.

Each atom represents a functional block with a typed boundary.
The communication structure emerges from the composition operators
(`∥`, `⊞`, `⊠`) applied to these atoms.
-/
inductive DHAtom : PortBoundary → Type where
  -- Protocol parties
  | alice : DHAtom bd
  | bob : DHAtom bd
  -- Communication infrastructure
  | channelAtoB : DHAtom bd
  | channelBtoA : DHAtom bd
  | adversary : DHAtom bd2
  -- Environment
  | environment : DHAtom bd2
  -- Ideal world
  | idealKE : DHAtom bd
  | simulator : DHAtom bd
  | dummyChannel : DHAtom bd2

private def renderDHAtom : ∀ {Δ : PortBoundary}, DHAtom Δ → String
  | _, .alice => "Alice"
  | _, .bob => "Bob"
  | _, .channelAtoB => "Channel A→B"
  | _, .channelBtoA => "Channel B→A"
  | _, .adversary => "Adversary"
  | _, .environment => "Environment"
  | _, .idealKE => "Ideal KE"
  | _, .simulator => "Simulator"
  | _, .dummyChannel => "Dummy Channel"

-- ============================================================================
-- § Communication infrastructure
-- ============================================================================

/-- Two directional channels running in parallel: Alice→Bob ∥ Bob→Alice. -/
@[show_composition]
def channels : Raw DHAtom bd2 :=
  .atom .channelAtoB ∥ .atom .channelBtoA

/--
Insecure network: the directional channels are wired through an adversary
who can observe or tamper with the traffic on both channels.

```
wire(par(Channel A→B, Channel B→A), Adversary)
```
-/
@[show_composition]
def insecureNetwork : Raw DHAtom bd2 :=
  channels ⊞ .atom .adversary

-- ============================================================================
-- § Real world
-- ============================================================================

/-- Protocol parties: Alice ∥ Bob. -/
@[show_composition]
def dhParties : Raw DHAtom bd2 :=
  .atom .alice ∥ .atom .bob

/--
Protocol execution: the parties are wired through the insecure network.
Alice's messages flow through the A→B channel (observed by the adversary)
to reach Bob, and vice versa through the B→A channel.

```
wire(par(Alice, Bob), wire(par(Ch A→B, Ch B→A), Adversary))
```
-/
@[show_composition]
def protocolExecution : Raw DHAtom bd2 :=
  dhParties ⊞ insecureNetwork

/--
Real world: the protocol execution is closed against the environment,
which drives both parties and reads their outputs.

```
plug(wire(par(Alice, Bob), insecureNetwork), Environment)
```
-/
@[show_composition]
def realWorld : Raw DHAtom PortBoundary.empty :=
  protocolExecution ⊠ .atom .environment

-- ============================================================================
-- § Ideal world
-- ============================================================================

/-- Ideal parties: the ideal key-exchange functionality ∥ the UC simulator. -/
@[show_composition]
def idealParties : Raw DHAtom bd2 :=
  .atom .idealKE ∥ .atom .simulator

/--
Ideal world: the ideal functionality and simulator are wired through a
dummy channel, then closed against the same environment.

UC security states that no polynomial-time environment can distinguish
`realWorld` from `idealWorld`.

```
plug(wire(par(Ideal KE, Simulator), Dummy Channel), Environment)
```
-/
@[show_composition]
def idealWorld : Raw DHAtom PortBoundary.empty :=
  idealParties ⊞ .atom .dummyChannel ⊠ .atom .environment

-- ============================================================================
-- § DOT output
-- ============================================================================

#eval IO.println "=== Real World ==="
#eval IO.println (Raw.toDot renderDHAtom realWorld)
#eval IO.println "=== Ideal World ==="
#eval IO.println (Raw.toDot renderDHAtom idealWorld)
