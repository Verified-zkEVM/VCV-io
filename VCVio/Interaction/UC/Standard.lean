/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.Computational
import VCVio.Interaction.UC.Notation

/-!
# Textbook UC vocabulary over the abstract open-system theory

This file gives a thin, presentation-layer reading of the abstract
`OpenTheory` / `Semantics` infrastructure in the standard Canetti-style
UC vocabulary: `Protocol`, `Functionality`, `Adversary`, `Environment`,
`Simulator`, and an explicit execution experiment `EXEC`.

The point of this file is *faithfulness*. The contextual-equivalence
form `CompEmulates ε π F` quantifies uniformly over arbitrary plugs
`K : T.Plug Δ`, which is mathematically clean but does not visibly look
like the textbook definition of UC security. The textbook form
`UCSecure ε π F` fixes that with explicit `∀ A. ∃ S. ∀ Z`-quantification
over real-world adversaries `A`, simulators `S`, and environments `Z`.

The bridge `compEmulates_toUCSecure_id` (this file) shows that
semantic emulation implies textbook UC security with the *identity*
simulator `S := A`, exposing a single plug
`K(A, Z) : T.Plug Δ.toPort` via `OpenTheory.plug_wire_left` and then
applying `CompEmulates` at that plug.

The converse direction (textbook UC implies plug-level
`CompUCSecure`) goes through Canetti's *dummy-adversary theorem* and
is recorded as the stated obligation `ucSecure_toCompUCSecure_dummy`.

## Main definitions

* `ProtocolBoundary`: a pair of port boundaries `(main, adv)` for the
  environment-facing and adversary-facing sides of a protocol.
* `ProtocolBoundary.toPort`: the combined `main ⊗ adv` port boundary.
* `Protocol T Δ`, `Functionality T Δ`: open systems exposing
  `Δ.toPort`.
* `Adversary T Δ back`: an open system at
  `swap Δ.adv ⊗ back`; the back-channel `back` carries communication
  between the adversary and the environment.
* `Environment T Δ back`: an open system at
  `swap Δ.main ⊗ swap back`, which is definitionally a
  `T.Plug (Δ.main ⊗ back)`.
* `Simulator T Δ back`: a function from real-world adversaries to
  ideal-world adversaries on the same back-channel.
* `dummyAdversary`: the canonical bidirectional relay
  `idWire Δ.adv : Adversary T Δ Δ.adv` from `HasIdWire`.
* `EXEC π A Z`: the closed system `T.close (T.wire π A) Z`.
* `UCSecure sem ε π F`: textbook computational UC security
  `∀ back A. ∃ S. ∀ Z. distAdvantage (EXEC π A Z) (EXEC F S Z) ≤ ε`.

## Main results

* `compEmulates_toUCSecure_id`: `CompEmulates sem ε π F` implies
  `UCSecure sem ε π F` with the identity simulator `S := A`.
-/

universe u

namespace Interaction
namespace UC
namespace Standard

variable {T : OpenTheory.{u}}

/-! ## Standard UC roles -/

/--
A protocol's *boundary signature*: a pair of port boundaries recording
the two directed interfaces a protocol exposes.

* `main` is the interface to the environment / honest parties (inputs
  in, outputs out).
* `adv` is the interface to the adversary / network (network packets,
  scheduling tokens, leakage, etc.).

Both sides are full `PortBoundary`s rather than bare `Interface`s
because each direction generally carries traffic in both directions.
-/
structure ProtocolBoundary where
  /-- Interface to the environment / honest parties. -/
  main : PortBoundary
  /-- Interface to the adversary / network. -/
  adv  : PortBoundary

namespace ProtocolBoundary

/-- The combined `main ⊗ adv` port boundary of a protocol. -/
abbrev toPort (Δ : ProtocolBoundary) : PortBoundary :=
  PortBoundary.tensor Δ.main Δ.adv

end ProtocolBoundary

variable {Δ : ProtocolBoundary} {back : PortBoundary}

/-- A *protocol* is an open system exposing its full
`(main ⊗ adv)` boundary. -/
abbrev Protocol (T : OpenTheory.{u}) (Δ : ProtocolBoundary) : Type u :=
  T.Obj Δ.toPort

/-- A *functionality* is the ideal-world counterpart of a protocol; the
same type, used as the trusted reference object. -/
abbrev Functionality (T : OpenTheory.{u}) (Δ : ProtocolBoundary) : Type u :=
  T.Obj Δ.toPort

/-- An *adversary* speaks to the protocol over the swapped `adv` side
and to the environment over a back-channel `back`. -/
abbrev Adversary (T : OpenTheory.{u}) (Δ : ProtocolBoundary)
    (back : PortBoundary) : Type u :=
  T.Obj (PortBoundary.tensor (PortBoundary.swap Δ.adv) back)

/-- An *environment* speaks to the protocol over the swapped `main`
side and to the adversary over the swapped back-channel. By
definitional equality of `swap` and `tensor`, this is exactly a
`T.Plug (PortBoundary.tensor Δ.main back)`. -/
abbrev Environment (T : OpenTheory.{u}) (Δ : ProtocolBoundary)
    (back : PortBoundary) : Type u :=
  T.Obj (PortBoundary.tensor
    (PortBoundary.swap Δ.main) (PortBoundary.swap back))

/-- A *simulator* maps a real-world adversary to an ideal-world
adversary on the same back-channel.

This is the lightweight presentation form. A more structural variant
keeps the simulator as an open system on
`Δ.adv ⊗ swap Δ.adv` and applies it via `wire`; both variants are
interconvertible in any compact-closed `OpenTheory`. -/
abbrev Simulator (T : OpenTheory.{u}) (Δ : ProtocolBoundary)
    (back : PortBoundary) : Type u :=
  Adversary T Δ back → Adversary T Δ back

/-- The *dummy adversary*: the canonical bidirectional relay between
the adversary's view of the protocol (`swap Δ.adv`) and the
environment's view of that same channel (`Δ.adv` on the back-channel).
It is the coevaluation `idWire Δ.adv` provided by `HasIdWire`. -/
def dummyAdversary [OpenTheory.HasIdWire T]
    (Δ : ProtocolBoundary) :
    Adversary T Δ Δ.adv :=
  OpenTheory.HasIdWire.idWire Δ.adv

/-! ## The execution experiment -/

/--
`EXEC π A Z` is the closed-system execution obtained by wiring the
protocol `π` to the adversary `A` along their shared `adv` boundary,
and then closing the result against the environment `Z`.

By definitional equality of `swap (X ⊗ Y)` with `swap X ⊗ swap Y`,
the type of `Z` is exactly the `T.Plug` of the wired result, so no
explicit boundary transport is needed.
-/
def EXEC (π : Protocol T Δ) (A : Adversary T Δ back)
    (Z : Environment T Δ back) : T.Closed :=
  T.close (T.wire π A) Z

/-! ## Textbook UC security -/

/--
`UCSecure sem ε π F` is the textbook computational UC security
statement: for every adversary `A`, there exists a simulator `S` such
that no environment `Z` can distinguish the real-world execution
`EXEC π A Z` from the ideal-world execution `EXEC F S Z` with
advantage greater than `ε`.

The quantifier structure `∀ back A. ∃ S. ∀ Z` is exactly Canetti's
formulation; in particular, the simulator may depend on the adversary
but not on the environment. The back-channel `back` is universally
quantified to allow the environment-adversary side-channel to be
arbitrary.
-/
def UCSecure (sem : Semantics T) (ε : ℝ)
    {Δ : ProtocolBoundary}
    (π F : Protocol T Δ) : Prop :=
  ∀ (back : PortBoundary) (A : Adversary T Δ back),
  ∃ S : Adversary T Δ back,
  ∀ Z : Environment T Δ back,
    sem.distAdvantage (EXEC π A Z) (EXEC F S Z) ≤ ε

/-! ## Bridge to abstract computational emulation -/

/--
Computational emulation `CompEmulates ε π F` implies textbook UC
security `UCSecure ε π F` with the **identity simulator** `S := A`:
the existential simulator is witnessed by the real-world adversary
itself.

The proof rewrites both `EXEC π A Z` and `EXEC F A Z` via
`OpenTheory.plug_wire_left`, exposing the *same* plug
`K(A, Z) : T.Plug Δ.toPort` on both sides, and then applies the
`CompEmulates` hypothesis at that single plug.
-/
theorem compEmulates_toUCSecure_id
    [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε : ℝ}
    {Δ : ProtocolBoundary} {π F : Protocol T Δ}
    (h : CompEmulates sem ε π F) :
    UCSecure sem ε π F :=
  fun _ A => ⟨A, fun Z => by
    change sem.distAdvantage (T.plug (T.wire π A) Z)
                              (T.plug (T.wire F A) Z) ≤ ε
    rw [OpenTheory.plug_wire_left, OpenTheory.plug_wire_left]
    exact h _⟩

/--
**Stated dummy-adversary direction.**

Textbook UC security `UCSecure ε π F` implies the plug-level
simulator-based form `CompUCSecure`: given the existential simulator
from `UCSecure` instantiated at the *dummy adversary*, one constructs
a `T.Plug Δ.toPort`-level simulator by repackaging the
adversary-environment pair through the zig-zag identity
`wire_idWire_right`.

This is the content of Canetti's dummy-adversary theorem (cf. Canetti
'01, Thm 4.16). Discharging this proof requires `IsCompactClosed T`
plus a structural decomposition of arbitrary plugs into
`(adversary, environment)` pairs; it is left as an explicit obligation
here so that the textbook quantifier structure can be presented now
without committing to the structural side of the proof.
-/
theorem ucSecure_toCompUCSecure_dummy
    [OpenTheory.IsCompactClosed T]
    {sem : Semantics T} {ε : ℝ}
    {Δ : ProtocolBoundary} {π F : Protocol T Δ}
    (_h : UCSecure sem ε π F) :
    ∃ (SimSpace : Type u) (simulate : SimSpace → T.Plug Δ.toPort →
        T.Plug Δ.toPort),
      CompUCSecure sem ε π F SimSpace simulate := by
  sorry

end Standard
end UC
end Interaction
