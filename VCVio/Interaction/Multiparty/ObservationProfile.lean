/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.Multiparty.Profile

/-!
# Observation-form profiles for compositional reasoning about disclosure

This file is the kernel-form analogue of `Multiparty/Profile.lean`. It
packages the **maximally general single-projection** form of a per-party
local-view decoration as a node context, and exposes the pointwise lift of
`Multiparty.Observation`'s information-lattice algebra to per-party profiles.

The motivation is **compositional reasoning about observation**:

* `ViewMode X` (the four-mode enumeration) is the operationally convenient
  form, with `rfl`-reducing `Action` shapes per pattern; it is the right
  input to `Profile.Strategy`.
* `Observation X = Σ Obs : Type u, X → Obs` is the semantically universal
  form, and the natural carrier for an algebra of observations: refinement
  is a Σ-factorization, coalition combination is a Σ-product, and
  corruption-indexed observation policies naturally produce
  `Observation`-valued maps `mode → party → Observation`.

`ObservationProfile.toViewProfile` lifts an observation profile back into a
`ViewProfile` via the universal `.react` constructor (`Observation.toViewMode`)
so that the existing `Profile.Strategy` pipeline can consume observation
profiles unchanged at the cost of dropping the operational `.pick` /
`.observe` / `.hidden` shapes. For mixed protocols where some parties want
those operational shapes, prefer building `ViewProfile`s directly and using
`ObservationProfile` only where the kernel algebra is needed.

## Pointwise information lattice

Because `Observation X` carries Mathlib's `Top`, `Bot`, `LE`, `Preorder`,
`OrderTop`, `OrderBot`, and `Max` instances (see `Multiparty/Observation.lean`),
the per-party profile type `Party → Observation X` automatically inherits
them pointwise via `Pi.preorder`, `Pi.instOrderTop`, `Pi.instOrderBot`, and
`Pi.instMax`. Concretely:

* `(⊤ : ObservationProfile Party X)` is the all-`Observation.top` profile
  (every party sees the entire move; top of the pointwise lattice);
* `(⊥ : ObservationProfile Party X)` is the all-`Observation.bot` profile
  (every party sees nothing; bottom);
* `k₁ ≤ k₂` means "`k₁` is no more revealing than `k₂` at every party"
  (`∀ p, (k₁ p).Refines (k₂ p)` by `Pi.le_def`);
* `k₁ ⊔ k₂` is the pointwise Σ-product, the **join**: each party gets the
  joint observation of `k₁ p` and `k₂ p`;
* `bot_le` and `le_top` come for free from the lifted `OrderBot` / `OrderTop`.

Per-party `Refines` is also still available as `(k₁ p).Refines (k₂ p)` for
explicit reasoning.

The dual meet (greatest common reduction) is not provided here for the same
reason as in `Multiparty/Observation.lean`: it requires quotienting `X` by
the joint indistinguishability relation, and the underlying `Refines` is
only a preorder (not antisymmetric).
-/

universe u v

namespace Interaction
namespace Multiparty
namespace Profile

/--
`ObservationProfile Party X` assigns to each party its observation kernel of
a node whose move space is `X`.

This is the kernel-form analogue of `ViewProfile`. The two are related by
`ObservationProfile.toViewProfile`, which lifts each per-party observation
into a `ViewMode` via the universal `.react` constructor
(`Observation.toViewMode`).

For most strategy-side use, work with `ViewProfile`. For compositional
reasoning about observation algebra (refinement, coalition combination,
corruption-indexed observation policies), build `ObservationProfile`s and
convert at the boundary.

The pointwise information-lattice algebra (`⊤`, `⊥`, `≤`, `⊔`, plus the
standard `bot_le` and `le_top` lemmas) is inherited from the per-party
`Observation X` instances via `Pi.preorder`, `Pi.instOrderTop`,
`Pi.instOrderBot`, and `Pi.instMax`.
-/
abbrev ObservationProfile (Party : Type u) : Spec.Node.Context.{u, u + 1} :=
  fun X => Party → Observation X

namespace ObservationProfile

variable {Party : Type u} {X : Type u}

/--
`ObservationProfile.toViewProfile k` lifts a per-party observation profile to
a per-party view profile via `Observation.toViewMode`.

Concretely each party's view becomes the universal `.react` form of its
observation. This is the bridge between the kernel-form algebra of
`ObservationProfile` and the endpoint-shape API of `ViewProfile` /
`Profile.Strategy`.

Caveat: this lifting forgets the operational `.pick` / `.observe` /
`.hidden` shapes. For protocols where a participant's endpoint should
genuinely have the `Σ-of-X` (pick) or function-from-X (observe) shape,
either build a mixed profile that uses `ViewMode` directly for those
parties, or compose the observation profile with a separate operational
decoration downstream.
-/
def toViewProfile (k : ObservationProfile Party X) : ViewProfile Party X :=
  fun p => Observation.toViewMode (k p)

@[simp] theorem toViewProfile_apply (k : ObservationProfile Party X) (p : Party) :
    toViewProfile k p = Observation.toViewMode (k p) := rfl

end ObservationProfile

end Profile
end Multiparty
end Interaction
