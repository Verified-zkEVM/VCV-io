/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Syntax
import VCVio.Interaction.Multiparty.Observation

/-!
# View modes: per-participant local-view shapes for multiparty interactions

This file introduces the smallest common local layer for multiparty
interaction in the `Interaction` framework, on top of the kernel-form
`Multiparty.Observation` algebra (`Multiparty/Observation.lean`).

The current two-party layer distinguishes between:
* the side that chooses the next move, and
* the side that receives that chosen move.

For adversarial and multiparty interaction, this is still not the whole story.
Besides:
* choosing the move,
* observing the full move, and
* observing nothing at all,

a participant may observe only a **quotient** or **projection** of the chosen
move. For example, a party might learn that a message was delivered on a given
channel without learning the payload itself.

The definitions in this file are intentionally local and minimal.

* `ViewMode X` records how one fixed participant locally sees a chosen move
  `x : X` at one node.
* `ViewMode.Action` is the canonical local node shape associated to that view.
* `ViewMode.toObservation` collapses a `ViewMode` into the maximally general
  single-projection form `Multiparty.Observation`.
* `Observation.toViewMode` lifts an arbitrary observation back into `ViewMode`
  via the universal `.react` constructor.
* `localSyntax` packages the four-mode `Action` shape as a `Spec.SyntaxOver`.
* `Strategy` is the induced whole-tree local endpoint type, obtained from
  arbitrary node-local metadata through `SyntaxOver.comap`.

Crucially, this file does **not** commit to any particular global communication
model. In particular, it does not choose between:
* broadcast / public-transcript interaction, where one party chooses and all
  others observe; or
* directed point-to-point interaction, where one party sends, one party
  receives, and the remaining parties are hidden or only partially informed.

Those models are recovered later by choosing different node decorations and
different resolvers.

## Two layers of observation: information lattice vs operational shape

`ViewMode` carries information along **two orthogonal axes**:

* an **information axis**: what observation does the participant make? This is
  fully captured by a single projection `toObs : X → Obs` packaged with its
  codomain `Obs`, i.e. by an `Observation X`. The induced ordering by
  informativeness gives a lattice with bottom `Observation.bot X` (no
  information) and top `Observation.top X = ⟨X, id⟩` (full information); see
  `Multiparty/Observation.lean`.
* an **operational axis**: how does the participant interact with that
  observation in continuation passing? Does it choose the move (effectful
  selection), wait for it (function-from-X), or commit to a uniform
  continuation family in advance (function-into-Cont)? This is encoded in the
  four constructors `pick`, `observe`, `hidden`, `react`, each of which
  specializes `Action` to a definitionally simpler shape.

### Why four constructors instead of two

A more parsimonious presentation would split the two axes completely: a
two-mode `pick | react Observation` `ViewMode`, with `observe` and `hidden`
recovered as `react (Observation.top X)` and `react (Observation.bot X)`
respectively. That presentation is informationally equivalent: `observe`
*morally is* `react Observation.top` and `hidden` *morally is*
`react Observation.bot`. They are precisely the two extremes of the
information lattice on `X`.

We deliberately keep all four constructors because the operational
specializations are **not definitionally equal** to their universal
react-form encodings. Compare:

```text
ViewMode.Action .observe m Cont   = (x : X) → m (Cont x)
Observation.Action ⟨X, id⟩ m Cont = (o : X) → m ((x : X) → x = o → Cont x)

ViewMode.Action .hidden m Cont                    = m ((x : X) → Cont x)
Observation.Action ⟨PUnit, fun _ => unit⟩ m Cont
                = (_ : PUnit) → m ((x : X) → unit = unit → Cont x)
```

The specialized forms are the ones that example endpoint computations want
to land on by `rfl`. Keeping `observe` and `hidden` as separate constructors
preserves those `rfl` reductions while still exposing the universal
`react`-form for genuinely arbitrary observations.

So the four constructors should be read as the two operational extremes of
the information lattice (`observe = top`, `hidden = bot`) plus one orthogonal
authorship-of-shape mode (`pick`, the `Σ-of-X` shape) and one universal
catch-all (`react`, the `Observation`-parameterized shape).

This file does **not** carry authorship-of-move information; that lives in
`Concurrent.NodeAuthority.controllers : X → List Party`, which credits each
possible move `x : X` with the (possibly multiple) parties responsible for
choosing it. In particular, the choice between `ViewMode.pick` and
`ViewMode.observe` is a *node shape* decision (effectful Σ-of-X vs
function-from-X), not the canonical authorship attribution.

## Literature

The kernel form `Σ Obs : Type, X → Obs` (here `Multiparty.Observation`)
arises in three independent traditions; see the docstring of
`Multiparty/Observation.lean` for citations. The closest type-theoretic
ancestor of the four-constructor operational shape is Hancock-Setzer
"Interactive Programs in Dependent Type Theory", whose Command/Response
interfaces with embedded observation modes mirror the
`pick` / `observe` / `hidden` / `react` taxonomy.

See `docs/agents/interaction.md` for the design rationale of the
information-vs-operational split.

Naming note: this file does not introduce a new global multiparty protocol
syntax. The existing `Interaction.Spec` already captures the global branching
structure. The multiparty layer only describes how one fixed participant
locally sees each node of such a spec.
-/

universe u v

namespace Interaction
namespace Multiparty

/--
`ViewMode X` is the local observation mode of one fixed participant at one
protocol node whose move space is `X`.

It answers the following question:

> Once a global protocol node has been fixed, how does the chosen participant
> locally experience the actual chosen move `x : X` of that node?

The possibilities are:
* `pick` — this participant locally selects the next move (effectful
  Σ-of-X shape for `Action`);
* `observe` — this participant is told the full chosen move and continues
  after seeing it (function-from-X shape for `Action`); informationally, this
  is the top of the observation lattice on `X`;
* `hidden` — this participant is not told the chosen move at the node itself,
  so any future behavior depending on that move must already be prepared
  uniformly over all possible moves; informationally, this is the bottom of
  the observation lattice;
* `react k` — the participant is told only the observation `k.2 x : k.1`
  exposed by the universal kernel `k : Observation X`. This is the universal
  `Action`-shape and subsumes all observation patterns not captured by
  `observe`/`hidden`.

These four constructors carry information along **two separate axes**:
* **operational** — they pick out four definitionally distinct `Action`
  shapes (see `ViewMode.Action`), enabling `rfl` reductions for common
  patterns;
* **observational** — they all collapse to a single observation kernel
  `X → Obs` packaged with its codomain (see `ViewMode.toObservation`).

Note that `observe` and `hidden` are operationally specialized cases of
`react`: morally `observe = react (Observation.top X)` and `hidden =
react (Observation.bot X)`. They are kept as separate constructors because
their specialized `Action` shapes are *not* definitionally equal to the
universal `react` form (see the file docstring), and protocol examples want
to land on the specialized shapes by `rfl`.

The operational distinction between `pick` and `observe` is **not** a
canonical authorship attribution. Authorship-of-move is recorded by
`Concurrent.NodeAuthority.controllers : X → List Party`, a *per-move* and
possibly *multi-controller* assignment. `ViewMode.pick` indicates only that a
participant chooses *locally* in its endpoint type; whether it is the
protocol-level controller of a particular move is recorded separately.

`ViewMode` is intentionally local. It does not describe the global
communication discipline that produced it, nor who else sees the move.

For protocols whose participants make arbitrary observations not captured by
the `pick` / `observe` / `hidden` patterns, prefer `react` (or build an
`Observation` directly and lift via `Observation.toViewMode`).
-/
inductive ViewMode (X : Type u) : Type (u + 1) where
  | pick
  | observe
  | hidden
  | react (k : Observation X)

namespace ViewMode

/--
`ObsType view` is the type of concrete observations made by a participant with
local view `view` when some actual move `x` occurs.

Reading by cases:
* for `pick` and `observe`, the participant learns the full move (the
  observation type is `X` itself, the top of the information lattice);
* for `hidden`, the participant learns nothing (`PUnit`, the bottom);
* for `react ⟨Obs, toObs⟩`, the participant learns the kernel observation
  `Obs`.

This packages the information content of a `ViewMode` independently from the
more structured endpoint semantics of `ViewMode.Action`.
-/
def ObsType {X : Type u} : ViewMode X → Type u
  | .pick => X
  | .observe => X
  | .hidden => PUnit
  | .react ⟨Obs, _⟩ => Obs

/--
`obsOf view x` is the concrete observation exposed by local view `view` when
the actual move was `x`.

This forgets any control or continuation structure and keeps only the
information that is revealed:
* `pick` and `observe` reveal the full move;
* `hidden` reveals nothing;
* `react ⟨_, toObs⟩` reveals `toObs x`.
-/
def obsOf {X : Type u} : (view : ViewMode X) → X → view.ObsType
  | .pick, x => x
  | .observe, x => x
  | .hidden, _ => PUnit.unit
  | .react ⟨_, toObs⟩, x => toObs x

/--
`ViewMode.Action view m Cont` is the canonical local node type for a fixed
participant with local view `view` at a node whose move space is `X`.

Interpretation by cases:
* if `view = pick`, the participant effectfully selects a move `x : X` and
  produces the matching continuation;
* if `view = observe`, the participant waits for the externally chosen move
  and then produces the continuation for that move;
* if `view = hidden`, the participant does not observe the chosen move at this
  node, so it must effectfully prepare an entire family of continuations, one
  for each possible move;
* if `view = react ⟨Obs, toObs⟩`, the participant is told only an observation
  `o : Obs`; it must then effectfully provide continuations for every move
  whose observation agrees with `o`. This is the universal shape.

This is the native multiparty analogue of `Interaction.Role.Action` from the
two-party layer, extended by hidden and partial-observation cases.
-/
def Action {X : Type u} (view : ViewMode X) (m : Type u → Type u)
    (Cont : X → Type u) : Type u :=
  match view with
  | .pick => m ((x : X) × Cont x)
  | .observe => (x : X) → m (Cont x)
  | .hidden => m ((x : X) → Cont x)
  | .react ⟨Obs, toObs⟩ => (o : Obs) → m ((x : X) → toObs x = o → Cont x)

/--
`toObservation v` is the canonical kernel form of `v`: it forgets the
operational `Action` shape and keeps only the observation type `Obs` and
projection `toObs : X → Obs`.

By construction:
* `.pick` and `.observe` both map to `Observation.top X = ⟨X, id⟩` (full
  information, top of the observation lattice);
* `.hidden` maps to `Observation.bot X = ⟨PUnit, fun _ => PUnit.unit⟩` (zero
  information, bottom of the lattice);
* `.react k` maps to `k`.

`.pick` and `.observe` collapse to the same observation because they differ
only in operational `Action` shape (effectful Σ-of-X vs function-from-X), not
in observation content. The "this party authors the move" semantics that one
might expect from `.pick` lives instead in
`Concurrent.NodeAuthority.controllers`.
-/
def toObservation {X : Type u} : ViewMode X → Observation X
  | .pick => Observation.top X
  | .observe => Observation.top X
  | .hidden => Observation.bot X
  | .react k => k

@[simp] theorem toObservation_pick {X : Type u} :
    toObservation (X := X) .pick = Observation.top X := rfl

@[simp] theorem toObservation_observe {X : Type u} :
    toObservation (X := X) .observe = Observation.top X := rfl

@[simp] theorem toObservation_hidden {X : Type u} :
    toObservation (X := X) .hidden = Observation.bot X := rfl

@[simp] theorem toObservation_react {X : Type u} (k : Observation X) :
    toObservation (.react k) = k := rfl

/--
The `ObsType` of a `ViewMode` agrees definitionally with the first projection
of its observation form, by case analysis.
-/
@[simp] theorem ObsType_eq_toObservation_fst {X : Type u} (v : ViewMode X) :
    v.ObsType = (toObservation v).1 := by
  cases v with
  | react k => rcases k with ⟨_, _⟩; rfl
  | _ => rfl

/--
The observation `obsOf v x` agrees with the kernel projection
`(toObservation v).snd x` (modulo the type identification of
`ObsType_eq_toObservation_fst`, hence stated as `HEq`).
-/
theorem obsOf_eq_toObservation_snd {X : Type u} (v : ViewMode X) (x : X) :
    HEq (obsOf v x) ((toObservation v).2 x) := by
  cases v with
  | react k => rcases k with ⟨_, _⟩; rfl
  | _ => rfl

/--
The `Action` shape of `.react ⟨Obs, toObs⟩` coincides definitionally with
the universal `Observation.Action` of the corresponding kernel.

This makes `.react` the universal `Action` shape: any protocol that builds
its endpoint with `Observation.Action` can equivalently work with
`ViewMode.Action (.react ⟨..⟩)`.
-/
@[simp] theorem Action_react_eq_Observation_Action {X : Type u}
    (k : Observation X)
    (m : Type u → Type u) (Cont : X → Type u) :
    ViewMode.Action (.react k) m Cont
      = Observation.Action k m Cont := by
  rcases k with ⟨_, _⟩
  rfl

end ViewMode

namespace Observation

/--
`k.toViewMode` canonically embeds an observation kernel `k = ⟨Obs, toObs⟩`
into `ViewMode` via the universal `.react` constructor.

`toViewMode` is a one-sided inverse of `ViewMode.toObservation`:
`(k.toViewMode).toObservation = k`. The reverse round-trip
`(v.toObservation).toViewMode` only equals `v` when `v` is itself a `.react`;
for `.pick` / `.observe` / `.hidden`, the round-trip lands on the
corresponding `.react` (those constructors carry operational shape
information that the kernel form deliberately discards, but their
information content is preserved as `Observation.top` / `Observation.bot`).
-/
def toViewMode {X : Type u} (k : Observation X) : ViewMode X :=
  .react k

@[simp] theorem toViewMode_eq_react {X : Type u} (k : Observation X) :
    toViewMode k = .react k := rfl

@[simp] theorem toObservation_toViewMode {X : Type u} (k : Observation X) :
    (toViewMode k).toObservation = k := rfl

end Observation

/--
`ViewModeContext` is the plain node context whose metadata at each node is
just one `ViewMode` of that node's move space.

This is the direct multiparty local-view analogue of the two-party
`RoleContext`.
More structured multiparty models usually decorate nodes by richer metadata
and then project that metadata to `ViewMode` via `SyntaxOver.comap`.
-/
abbrev ViewModeContext : Spec.Node.Context.{u, u + 1} := fun X : Type u => ViewMode X

/--
`localSyntax m` is the fundamental local syntax for one fixed participant when
the node metadata already is that participant's `ViewMode`.

At a node with move space `X`, view `v : ViewMode X`, and continuation family
`Cont : X → Type`, the local node object is exactly `v.Action m Cont`.

This syntax uses the singleton agent type `PUnit`, because it describes the
endpoint of one fixed participant viewpoint rather than a whole participant
profile.
-/
def localSyntax (m : Type u → Type u) :
    Spec.SyntaxOver (PUnit : Type) (fun X : Type u => ViewMode X) where
  Node _ _ view Cont := view.Action m Cont

/--
`Strategy m resolve spec ctxs Output` is the whole-tree local endpoint type for
one fixed participant in a multiparty interaction.

Inputs:
* `Γ` is any chosen node-local metadata context;
* `resolve : Γ → ViewMode` explains how the fixed participant locally sees a
  node carrying metadata `γ : Γ X`;
* `ctxs : Spec.Decoration Γ spec` supplies that metadata across the protocol
  tree.

The endpoint type is then obtained by reusing `localSyntax m` through
`SyntaxOver.comap resolve`.

So a `Strategy` here is **not** a global profile of all participants.
It is the projected local behavior of one chosen participant viewpoint.
Different multiparty communication models are recovered by choosing different
metadata contexts `Γ`, decorations `ctxs`, and resolvers `resolve`.
-/
abbrev Strategy
    (m : Type u → Type u)
    {Γ : Spec.Node.Context.{u, v}}
    (resolve : Spec.Node.ContextHom Γ (fun X : Type u => ViewMode X))
    (spec : Spec) (ctxs : Spec.Decoration Γ spec)
    (Output : Spec.Transcript spec → Type u) :=
  Spec.SyntaxOver.Family ((localSyntax m).comap resolve) PUnit.unit spec ctxs Output

end Multiparty
end Interaction
