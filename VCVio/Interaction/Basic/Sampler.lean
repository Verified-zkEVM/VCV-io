/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.Basic.Decoration

/-!
# Monadic samplers on interaction specs

A `Spec.Sampler m spec` equips every node of a protocol tree `spec : Spec.{w}`
with an `m`-computation producing that node's move. Structurally it is a
`Spec.Decoration` whose per-node context is `fun X => m X`, so the full
`Decoration` API (map, map_id, map_comp, …) applies unchanged.

This file defines the `Sampler` abbreviation, the universal `sampleTranscript`
routine that threads a sampler through a spec to produce a full transcript,
and `Sampler.interleave`, which is the sampling counterpart of
`ProcessOver.interleave`: combine a scheduler sampler (`m (ULift Bool)`)
with two branch samplers into a sampler for the binary-choice interleaving
spec. The latter is the structural ingredient that lets `openTheory m`'s
`par`, `wire`, and `plug` operations thread per-node samplers compositionally.

Everything here is monad-generic and universe-polymorphic: the intermediate
monad is `m : Type w → Type w'`, the spec lives at the move universe `Spec.{w}`,
and the sampler's decoration values live at `Type w'`. Probability-monad-specific
constructions (e.g., `Sampler.uniform` over a `Spec.Fintype` ornament) live in
the runtime layer where `ProbComp` is in scope.
-/

universe w w'

namespace Interaction

namespace Spec

/--
A `Sampler` for `spec : Spec.{w}` provides an `m X` computation at each
node whose move space is `X`, plus recursive samplers for every subtree.

Structurally this is exactly a `Spec.Decoration` whose node context is
`fun X => m X`: the per-node decoration stores an `m`-computation in
the move type of that node, and the functorial `Decoration.map` /
`Decoration.map_id` / `Decoration.map_comp` API applies immediately.

The intermediate monad `m : Type w → Type w'` carries the execution
effects. Typical choices:
* `ProbComp : Type → Type` for coin-flip-only protocols.
* `OracleComp (unifSpec + roSpec) : Type → Type` for protocols with
  shared random oracle access, where samplers can issue oracle queries
  via `query`.
* `OptionT ProbComp : Type → Type` for observation-style semantics that
  need to inject failure mass.
-/
abbrev Sampler (m : Type w → Type w') (spec : Spec.{w}) : Type (max w w') :=
  Decoration (fun X => m X) spec

/--
Execute a sampler to produce a full transcript of `spec` in the monad `m`.

At each node the sampler monadically chooses a move; that move determines
which subtree to continue sampling.
-/
def sampleTranscript {m : Type w → Type w'} [Monad m] :
    (spec : Spec.{w}) → Sampler m spec → m (Transcript spec)
  | .done, _ => pure ⟨⟩
  | .node _ rest, ⟨samp, sampRest⟩ => do
      let x ← samp
      let tr ← sampleTranscript (rest x) (sampRest x)
      return ⟨x, tr⟩

/--
Combine a scheduler sampler with two per-branch samplers into a sampler
for the binary-choice interleaving spec
`Spec.node (ULift Bool) (fun ⟨true⟩ => spec₁ | ⟨false⟩ => spec₂)`.

This is the sampling counterpart of `Concurrent.ProcessOver.interleave`:
the scheduler flips a coin in `m` to pick a branch, and then the chosen
branch's sampler runs to produce the remainder of the transcript.

`openTheory m`'s `par`, `wire`, and `plug` all combine two open processes
via a binary-choice scheduling node, and `Sampler.interleave` threads the
per-step samplers through that node compositionally.
-/
def Sampler.interleave {m : Type w → Type w'}
    {spec₁ spec₂ : Spec.{w}}
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (sampler₁ : Sampler m spec₁)
    (sampler₂ : Sampler m spec₂) :
    Sampler m (Spec.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => spec₁
      | ⟨false⟩ => spec₂) :=
  ⟨schedulerSampler, fun
    | ⟨true⟩ => sampler₁
    | ⟨false⟩ => sampler₂⟩

end Spec

end Interaction
