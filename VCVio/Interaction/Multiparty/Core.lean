/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Syntax

/-!
# Native local views for multiparty interactions

This file introduces the smallest common local layer for multiparty
interaction in the `Interaction` framework.

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

* `LocalView X` records how one fixed participant locally sees a chosen move
  `x : X` at one node.
* `LocalView.Action` is the canonical local node shape associated to that view.
* `LocalView.Kernel` is the **maximally general single-projection form** of a
  local view, packaging just the observation type and projection function.
  Every `LocalView` collapses to a `Kernel` via `LocalView.toKernel`.
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

## Two layers of observation: kernel vs operational shape

`LocalView` carries information along **two orthogonal axes**:

* an **information axis**: what observation does the participant make? This is
  fully captured by a single projection `toObs : X → Obs` packaged with its
  codomain `Obs`. We call this the *kernel* of the local view; see
  `LocalView.Kernel`.
* an **operational axis**: how does the participant interact with that
  observation in continuation passing? Does it choose the move (effectful
  selection), wait for it (function-from-X), or commit to a uniform
  continuation family in advance (function-into-Cont)? This is encoded in the
  four constructors `active`, `observe`, `hidden`, `quotient`, each of which
  specializes `Action` to a definitionally simpler shape.

The four-constructor enumeration is the *ergonomically convenient* form for
common patterns: it lets `LocalView.Action` reduce by `rfl` for each pattern,
which keeps protocol examples short. `LocalView.Kernel` is the *semantically
universal* form: any `LocalView` collapses to a kernel, and protocols that
need only the observation can build kernels directly.

This file does **not** carry authorship-of-move information; that lives in
`Concurrent.NodeAuthority.controllers : Party → Bool`. In particular, the
choice between `LocalView.active` and `LocalView.observe` is a *node shape*
decision (effectful Σ-of-X vs function-from-X), not the canonical predicate
for "this party authors the move".

## Literature

Three independent literature traditions converge on the kernel form
`Σ Obs : Type, X → Obs`:

* Halpern-Vardi epistemic logic ("Reasoning About Knowledge"): agent
  observation as a projection from global state to local indistinguishability
  classes;
* Goguen-Meseguer noninterference / Sabelfeld-Myers info-flow: per-level
  projection of observable outputs;
* Honda-Yoshida-Carbone multiparty session types and Cruz-Filipe-Montesi
  endpoint projection: projection of a global type / global play to a single
  role's local view;
* Hancock-Setzer interactive interfaces: the type-theoretic ancestor of the
  four-constructor operational shape (Command/Response with embedded
  observation modes).

See `docs/agents/interaction.md` for a brief literature map and the design
rationale for the kernel-vs-operational split.

Naming note:
this file does not introduce a new global multiparty protocol syntax. The
existing `Interaction.Spec` already captures the global branching structure.
The multiparty layer only describes how one fixed participant locally sees each
node of such a spec.
-/

universe u v

namespace Interaction
namespace Multiparty

/--
`LocalView X` is the local observation mode of one fixed participant at one
protocol node whose move space is `X`.

It answers the following question:

> Once a global protocol node has been fixed, how does the chosen participant
> locally experience the actual chosen move `x : X` of that node?

The possibilities are:
* `active` — this participant locally selects the next move (effectful
  Σ-of-X shape for `Action`);
* `observe` — this participant is told the full chosen move and continues
  after seeing it (function-from-X shape for `Action`);
* `hidden` — this participant is not told the chosen move at the node itself,
  so any future behavior depending on that move must already be prepared
  uniformly over all possible moves;
* `quotient Obs toObs` — this participant is told only the observation
  `toObs x : Obs`, not the full move `x`.

These four constructors carry information along **two separate axes**:
* **operational** — they pick out four definitionally distinct `Action` shapes
  (see `LocalView.Action`), enabling `rfl` reductions for common patterns;
* **observational** — they all collapse to a single quotient morphism
  `X → Obs` packaged with its codomain (see `LocalView.Kernel`).

The operational distinction between `active` and `observe` is **not** a
canonical authorship predicate. Authorship-of-move is recorded by
`Concurrent.NodeAuthority.controllers : Party → Bool`. `LocalView.active`
indicates that a participant chooses *locally* in its endpoint type; whether
it is the protocol-level controller is recorded separately.

`LocalView` is intentionally local. It does not describe the global
communication discipline that produced it, nor who else sees the move.

For protocols whose participants make arbitrary observations not captured by
the `active`/`observe`/`hidden` patterns, prefer `LocalView.Kernel` directly:
it is the maximally general observation primitive.
-/
inductive LocalView (X : Type u) : Type (u + 1) where
  | active
  | observe
  | hidden
  | quotient (Obs : Type u) (toObs : X → Obs)

namespace LocalView

/--
`ObsType view` is the type of concrete observations made by a participant with
local view `view` when some actual move `x` occurs.

Reading by cases:
* for `active` and `observe`, the participant learns the full move;
* for `hidden`, the participant learns nothing (`PUnit`);
* for `quotient Obs toObs`, the participant learns only the quotient
  observation `toObs x : Obs`.

This packages the information content of a `LocalView` independently from the
more structured endpoint semantics of `LocalView.Action`.
-/
def ObsType {X : Type u} : LocalView X → Type u
  | .active => X
  | .observe => X
  | .hidden => PUnit
  | .quotient Obs _ => Obs

/--
`obsOf view x` is the concrete observation exposed by local view `view` when
the actual move was `x`.

This forgets any control or continuation structure and keeps only the
information that is revealed:
* `active` and `observe` reveal the full move;
* `hidden` reveals nothing;
* `quotient Obs toObs` reveals `toObs x`.
-/
def obsOf {X : Type u} : (view : LocalView X) → X → view.ObsType
  | .active, x => x
  | .observe, x => x
  | .hidden, _ => PUnit.unit
  | .quotient _ toObs, x => toObs x

/--
`LocalView.Action view m Cont` is the canonical local node type for a fixed
participant with local view `view` at a node whose move space is `X`.

Interpretation by cases:
* if `view = active`, the participant effectfully selects a move `x : X` and
  produces the matching continuation;
* if `view = observe`, the participant waits for the externally chosen move
  and then produces the continuation for that move;
* if `view = hidden`, the participant does not observe the chosen move at this
  node, so it must effectfully prepare an entire family of continuations, one
  for each possible move;
* if `view = quotient Obs toObs`, the participant is told only an observation
  `o : Obs`; it must then effectfully provide continuations for every move
  whose observation agrees with `o`.

This is the native multiparty analogue of `Interaction.Role.Action` from the
two-party layer, extended by hidden and partial-observation cases.
-/
def Action {X : Type u} (view : LocalView X) (m : Type u → Type u)
    (Cont : X → Type u) : Type u :=
  match view with
  | .active => m ((x : X) × Cont x)
  | .observe => (x : X) → m (Cont x)
  | .hidden => m ((x : X) → Cont x)
  | .quotient Obs toObs => (o : Obs) → m ((x : X) → toObs x = o → Cont x)

/--
`LocalView.Kernel X` is the **polynomial-element** form of a local view: a
single quotient morphism `toObs : X → Obs` packaged with its codomain `Obs`.

This is the maximally general "what does a participant see" primitive. Three
independent literature traditions converge on this exact object: epistemic
logic (Halpern-Vardi), noninterference / info-flow (Goguen-Meseguer,
Sabelfeld-Myers), and session-type / endpoint-projection frameworks
(Honda-Yoshida-Carbone, Cruz-Filipe-Montesi).

Every `LocalView X` collapses to a `Kernel X` via `LocalView.toKernel`,
forgetting only the operational `Action` shape (the four-constructor
enumeration is more ergonomic for `Action`-shape `rfl` reductions, but carries
the same observational content as the corresponding kernel).

Use `Kernel` directly when the protocol carries arbitrary observation types
not captured by `active` / `observe` / `hidden`. Use `LocalView` when those
specialized operational shapes are wanted.
-/
abbrev Kernel (X : Type u) : Type (u + 1) := Σ Obs : Type u, X → Obs

namespace Kernel

variable {X : Type u}

/--
`Kernel.Action k m Cont` is the maximally general local node shape associated
to a kernel `k = ⟨Obs, toObs⟩`.

It coincides definitionally with `LocalView.Action (.quotient Obs toObs) m Cont`
(see `LocalView.Action_quotient_eq_kernel_Action`).
-/
def Action (k : Kernel X) (m : Type u → Type u) (Cont : X → Type u) : Type u :=
  (o : k.1) → m ((x : X) → k.2 x = o → Cont x)

end Kernel

/--
`toKernel v` is the canonical kernel form of a `LocalView v`: it forgets the
operational `Action` shape and keeps only the observation type `Obs` and
projection `toObs : X → Obs`.

By construction:
* `.active` and `.observe` both map to `⟨X, id⟩` (full information);
* `.hidden` maps to `⟨PUnit, fun _ => PUnit.unit⟩` (zero information);
* `.quotient Obs toObs` maps to `⟨Obs, toObs⟩`.

`.active` and `.observe` collapse to the same kernel because they differ only
in operational `Action` shape (effectful Σ-of-X vs function-from-X), not in
observation content. The "this party authors the move" semantics that one
might expect from `.active` lives instead in
`Concurrent.NodeAuthority.controllers`.
-/
def toKernel {X : Type u} : LocalView X → Kernel X
  | .active => ⟨X, id⟩
  | .observe => ⟨X, id⟩
  | .hidden => ⟨PUnit, fun _ => PUnit.unit⟩
  | .quotient Obs toObs => ⟨Obs, toObs⟩

@[simp] theorem toKernel_active {X : Type u} :
    toKernel (X := X) .active = ⟨X, id⟩ := rfl

@[simp] theorem toKernel_observe {X : Type u} :
    toKernel (X := X) .observe = ⟨X, id⟩ := rfl

@[simp] theorem toKernel_hidden {X : Type u} :
    toKernel (X := X) .hidden = ⟨PUnit, fun _ => PUnit.unit⟩ := rfl

@[simp] theorem toKernel_quotient {X : Type u} (Obs : Type u) (toObs : X → Obs) :
    toKernel (.quotient Obs toObs) = ⟨Obs, toObs⟩ := rfl

/--
The `ObsType` of a `LocalView` agrees definitionally with the first projection
of its kernel form, by case analysis.
-/
@[simp] theorem ObsType_eq_toKernel_fst {X : Type u} (v : LocalView X) :
    v.ObsType = (toKernel v).1 := by
  cases v <;> rfl

/--
The observation `obsOf v x` agrees with the kernel-form projection
`(toKernel v).snd x` (modulo the type identification of
`ObsType_eq_toKernel_fst`, hence stated as `HEq`).
-/
theorem obsOf_eq_toKernel_snd {X : Type u} (v : LocalView X) (x : X) :
    HEq (obsOf v x) ((toKernel v).2 x) := by
  cases v <;> rfl

/--
The `Action` shape of `.quotient Obs toObs` coincides definitionally with the
maximally general `Kernel.Action` of the corresponding kernel.

This makes `.quotient` the universal `Action` shape: any protocol that builds
its endpoint with `Kernel.Action` can equivalently work with
`LocalView.Action (.quotient ..)`.
-/
@[simp] theorem Action_quotient_eq_kernel_Action {X : Type u}
    (Obs : Type u) (toObs : X → Obs)
    (m : Type u → Type u) (Cont : X → Type u) :
    LocalView.Action (.quotient Obs toObs) m Cont
      = Kernel.Action ⟨Obs, toObs⟩ m Cont := rfl

/--
`fromKernel k` canonically embeds a kernel `k = ⟨Obs, toObs⟩` into `LocalView`
via the universal `.quotient` constructor.

`fromKernel` is a one-sided inverse of `toKernel`:
`toKernel (fromKernel k) = k`. The reverse round-trip
`fromKernel (toKernel v)` only equals `v` when `v` is itself a `.quotient`;
for `.active` / `.observe` / `.hidden`, the round-trip lands on the
corresponding `.quotient`, which is intended (those constructors carry
operational shape information that the kernel form deliberately discards).
-/
def fromKernel {X : Type u} : Kernel X → LocalView X
  | ⟨Obs, toObs⟩ => .quotient Obs toObs

@[simp] theorem toKernel_fromKernel {X : Type u} (k : Kernel X) :
    toKernel (fromKernel k) = k := by
  rcases k with ⟨Obs, toObs⟩
  rfl

end LocalView

/--
`LocalViewContext` is the plain node context whose metadata at each node is
just one `LocalView` of that node's move space.

This is the direct multiparty local-view analogue of the two-party
`RoleContext`.
More structured multiparty models usually decorate nodes by richer metadata and
then project that metadata to `LocalView` via `SyntaxOver.comap`.
-/
abbrev LocalViewContext : Spec.Node.Context.{u, u + 1} := fun X : Type u => LocalView X

/--
`localSyntax m` is the fundamental local syntax for one fixed participant when
the node metadata already is that participant's `LocalView`.

At a node with move space `X`, view `v : LocalView X`, and continuation family
`Cont : X → Type`, the local node object is exactly `v.Action m Cont`.

This syntax uses the singleton agent type `PUnit`, because it describes the
endpoint of one fixed participant viewpoint rather than a whole participant
profile.
-/
def localSyntax (m : Type u → Type u) :
    Spec.SyntaxOver (PUnit : Type) (fun X : Type u => LocalView X) where
  Node _ _ view Cont := view.Action m Cont

/--
`Strategy m resolve spec ctxs Output` is the whole-tree local endpoint type for
one fixed participant in a multiparty interaction.

Inputs:
* `Γ` is any chosen node-local metadata context;
* `resolve : Γ → LocalView` explains how the fixed participant locally sees a
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
    (resolve : Spec.Node.ContextHom Γ (fun X : Type u => LocalView X))
    (spec : Spec) (ctxs : Spec.Decoration Γ spec)
    (Output : Spec.Transcript spec → Type u) :=
  Spec.SyntaxOver.Family ((localSyntax m).comap resolve) PUnit.unit spec ctxs Output

end Multiparty
end Interaction
