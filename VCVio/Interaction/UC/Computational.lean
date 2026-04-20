/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.Emulates
import VCVio.CryptoFoundations.Asymptotics.Negligible
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.EvalDist.Defs.Semantics
import VCVio.EvalDist.TVDist

/-!
# Computational observation layer for UC security

This file gives a concrete computational reading of the abstract UC
judgments (`Emulates`, `UCSecure`) in terms of distributional
distinguishing advantage. It deliberately keeps the fixed-`ε` notion
`CompEmulates` separate from the abstract `Emulates`-as-equivalence
judgment, because the relation
`fun c₁ c₂ => tvDist (sem c₁) (sem c₂) ≤ ε` is not transitive at fixed
`ε` (the triangle inequality only gives `2ε`) and therefore cannot be
packaged as `Observation T`. The principled bridge to abstract
`Emulates` lives at the asymptotic level (`AsympCompEmulates`), where
sums of negligibles are still negligible.

## Design: bundled sub-probabilistic semantics

A `Semantics T` bundles:

1. an ambient surface monad `m : Type → Type` in which closed systems
   are observed;
2. a `SPMFSemantics m` factoring computations in `m` through an internal
   semantic monad into an externally visible `SPMF`;
3. a `run : T.Closed → m Unit` that extracts the probabilistic game
   associated to each closed system.

The observation target is `SPMF Unit`, so the resulting denotation
carries genuine failure mass. Distinguishing advantage is the total
variation distance between the two resulting `SPMF Unit` distributions.
This lets the same framework express:

* coin-flip-only protocols with `m = ProbComp` and
  `SPMFSemantics.ofHasEvalSPMF ProbComp`;
* protocols with shared oracles where `m = OracleComp superSpec` and
  the internal semantic monad is `StateT σ ProbComp` via `simulateQ`;
* observation-style semantics that deliberately introduce failure, for
  example by querying with `OptionT ProbComp` and `guard`-ing on a
  predicate over sampled values. This is how OTP-style privacy gets a
  non-vacuous `CompEmulates 0` discharge.

## Main definitions

* `Semantics T` bundles a surface monad, its sub-probabilistic
  semantics, and a `run` function extracting a game from each closed
  system.
* `Semantics.evalDist` is the `SPMF Unit` denotation of a closed system.
* `Semantics.distAdvantage` is the total variation distance between two
  such denotations, and the replacement for the old
  `ProbComp.distAdvantage` pivot.
* `CompEmulates sem ε real ideal` asserts that for every environment
  (plug), the distinguishing advantage between the real and ideal
  closed systems is at most `ε`.
* `AsympCompEmulates` is the asymptotic variant: for every PPT
  adversary choosing environments, the advantage is negligible in the
  security parameter.
* `CompUCSecure sem ε protocol ideal SimSpace simulate` is the
  simulator-based variant with bounded advantage.

## Main results

* `CompEmulates.refl`: advantage zero against itself.
* `CompEmulates.triangle`: transitivity with additive advantage bounds.
* `CompEmulates.map_invariance`: boundary adaptation preserves the bound.
* `CompEmulates.par_compose`, `wire_compose`, `plug_compose`:
  advantages add under parallel, wired, and plugged composition.
* `CompUCSecure.toCompEmulates_id`: simulator-based security with the
  identity simulator recovers computational emulation.
* `AsympCompEmulates.par_compose`, `wire_compose`, `plug_compose`:
  asymptotic composition from pointwise negligible bounds.
* `ucDistGame`: constructs the `SecurityGame` whose advantage is the
  UC distinguishing advantage.
* `AsympCompEmulates.iff_secureAgainst`: `AsympCompEmulates` is
  equivalent to security of the UC distinguishing game.
-/

universe u

open OracleComp ENNReal

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/--
`Semantics T` bundles a computational observation layer for closed
systems in the open-composition theory `T`:

* `m` is the surface monad in which the observation is written;
* `sem` is a `SPMFSemantics m` giving `m` its sub-probabilistic
  meaning;
* `run` extracts a `m Unit` game from each closed system.

The visible denotation of a closed system is therefore a
`SPMF Unit`, where the `none` branch records failure mass (for example,
a `guard` that rejected the sampled value). Distinguishing advantage
is total variation on those `SPMF Unit` distributions.
-/
structure Semantics (T : OpenTheory.{u}) where
  /-- Surface monad in which closed systems are observed. -/
  m : Type → Type
  /-- Monad structure on the surface monad. -/
  instMonad : Monad m
  /-- Bundled sub-probabilistic semantics for the surface monad. The
  internal semantic monad is kept in `Type → Type` so that every
  protocol (`ProbComp`, `OracleComp superSpec`, `OptionT ProbComp`,
  `StateT σ ProbComp`) fits uniformly. -/
  sem : SPMFSemantics.{0, 0, 0} m
  /-- The probabilistic game extracted from a closed system. -/
  run : T.Closed → m Unit

attribute [instance] Semantics.instMonad

namespace Semantics

variable {S : Semantics T}

/-- The external `SPMF Unit` denotation of a closed system under `S`. -/
noncomputable def evalDist (S : Semantics T) (p : T.Closed) : SPMF Unit :=
  S.sem.evalDist (S.run p)

/-- Distinguishing advantage between two closed systems under `S`,
defined as the total variation distance of their `SPMF Unit`
denotations. -/
noncomputable def distAdvantage (S : Semantics T) (p q : T.Closed) : ℝ :=
  SPMF.tvDist (S.evalDist p) (S.evalDist q)

@[simp]
lemma distAdvantage_self (S : Semantics T) (p : T.Closed) :
    S.distAdvantage p p = 0 := SPMF.tvDist_self _

lemma distAdvantage_comm (S : Semantics T) (p q : T.Closed) :
    S.distAdvantage p q = S.distAdvantage q p := SPMF.tvDist_comm _ _

lemma distAdvantage_nonneg (S : Semantics T) (p q : T.Closed) :
    0 ≤ S.distAdvantage p q := SPMF.tvDist_nonneg _ _

lemma distAdvantage_triangle (S : Semantics T) (p q r : T.Closed) :
    S.distAdvantage p r ≤ S.distAdvantage p q + S.distAdvantage q r :=
  SPMF.tvDist_triangle _ _ _

lemma distAdvantage_le_one (S : Semantics T) (p q : T.Closed) :
    S.distAdvantage p q ≤ 1 := SPMF.tvDist_le_one _ _

end Semantics

/--
`CompEmulates sem ε real ideal` asserts that `real` computationally
emulates `ideal` up to advantage `ε` under semantics `sem`.

For every plug `K : T.Plug Δ`, the total variation distance between the
real-world and ideal-world closed-system denotations is at most `ε`.
-/
def CompEmulates (sem : Semantics T) (ε : ℝ)
    {Δ : PortBoundary} (real ideal : T.Obj Δ) : Prop :=
  ∀ K : T.Plug Δ,
    sem.distAdvantage (T.close real K) (T.close ideal K) ≤ ε

namespace CompEmulates

/--
Every system computationally emulates itself with advantage zero.
-/
theorem refl (sem : Semantics T) {Δ : PortBoundary} (W : T.Obj Δ) :
    CompEmulates sem 0 W W :=
  fun _ => by simp

/--
Computational emulation composes transitively with additive advantage
bounds (triangle inequality on total variation distance).
-/
theorem triangle {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ : PortBoundary} {W₁ W₂ W₃ : T.Obj Δ}
    (h₁₂ : CompEmulates sem ε₁ W₁ W₂)
    (h₂₃ : CompEmulates sem ε₂ W₂ W₃) :
    CompEmulates sem (ε₁ + ε₂) W₁ W₃ :=
  fun K => calc
    sem.distAdvantage (T.close W₁ K) (T.close W₃ K)
      ≤ sem.distAdvantage (T.close W₁ K) (T.close W₂ K) +
        sem.distAdvantage (T.close W₂ K) (T.close W₃ K) :=
          sem.distAdvantage_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add (h₁₂ K) (h₂₃ K)

/--
Adapting both sides of a computational emulation along the same boundary
morphism preserves the advantage bound.

This is the computational specialization of `Emulates.map_invariance`.
The key identity is `plug (map f W) K = plug W (map (swap f) K)`.
-/
theorem map_invariance [OpenTheory.IsLawfulPlug T]
    {sem : Semantics T} {ε : ℝ}
    {Δ₁ Δ₂ : PortBoundary}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    {real ideal : T.Obj Δ₁}
    (h : CompEmulates sem ε real ideal) :
    CompEmulates sem ε (T.map f real) (T.map f ideal) :=
  fun K => by
    simp only [OpenTheory.close,
      OpenTheory.map_plug f real K, OpenTheory.map_plug f ideal K]
    exact h _

/--
Weakening: if `ε₁ ≤ ε₂` then `CompEmulates sem ε₁` implies
`CompEmulates sem ε₂`.
-/
theorem mono {sem : Semantics T} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {Δ : PortBoundary} {real ideal : T.Obj Δ}
    (h : CompEmulates sem ε₁ real ideal) :
    CompEmulates sem ε₂ real ideal :=
  fun K => le_trans (h K) hε

/-! ### Composition -/

/-- Replacing the left component of a parallel composition preserves the
computational emulation bound. -/
theorem par_left [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε : ℝ}
    {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : T.Obj Δ₁}
    (h₁ : CompEmulates sem ε real₁ ideal₁)
    (W₂ : T.Obj Δ₂) :
    CompEmulates sem ε (T.par real₁ W₂) (T.par ideal₁ W₂) :=
  fun K => by
    rw [OpenTheory.close_par_left, OpenTheory.close_par_left]
    exact h₁ _

/-- Replacing the right component of a parallel composition preserves the
computational emulation bound. -/
theorem par_right [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε : ℝ}
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : T.Obj Δ₁)
    {real₂ ideal₂ : T.Obj Δ₂}
    (h₂ : CompEmulates sem ε real₂ ideal₂) :
    CompEmulates sem ε (T.par W₁ real₂) (T.par W₁ ideal₂) :=
  fun K => by
    rw [OpenTheory.close_par_right, OpenTheory.close_par_right]
    exact h₂ _

/-- **Computational UC composition for `par`**: advantages add. -/
theorem par_compose [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : T.Obj Δ₁} {real₂ ideal₂ : T.Obj Δ₂}
    (h₁ : CompEmulates sem ε₁ real₁ ideal₁)
    (h₂ : CompEmulates sem ε₂ real₂ ideal₂) :
    CompEmulates sem (ε₁ + ε₂) (T.par real₁ real₂) (T.par ideal₁ ideal₂) :=
  triangle (par_left h₁ real₂) (par_right ideal₁ h₂)

/-- Replacing the left factor of a wiring preserves the computational
emulation bound. -/
theorem wire_left [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε : ℝ}
    {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    (h₁ : CompEmulates sem ε real₁ ideal₁)
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    CompEmulates sem ε (T.wire real₁ W₂) (T.wire ideal₁ W₂) :=
  fun K => by
    rw [OpenTheory.close_wire_left, OpenTheory.close_wire_left]
    exact h₁ _

/-- Replacing the right factor of a wiring preserves the computational
emulation bound. -/
theorem wire_right [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε : ℝ}
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₂ : CompEmulates sem ε real₂ ideal₂) :
    CompEmulates sem ε (T.wire W₁ real₂) (T.wire W₁ ideal₂) :=
  fun K => by
    rw [OpenTheory.close_wire_right, OpenTheory.close_wire_right]
    exact h₂ _

/-- **Computational UC composition for `wire`**: advantages add. -/
theorem wire_compose [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : CompEmulates sem ε₁ real₁ ideal₁)
    (h₂ : CompEmulates sem ε₂ real₂ ideal₂) :
    CompEmulates sem (ε₁ + ε₂) (T.wire real₁ real₂) (T.wire ideal₁ ideal₂) :=
  triangle (wire_left h₁ real₂) (wire_right ideal₁ h₂)

/-- **Computational UC composition for `plug`**: when both the protocol
and the environment emulate their ideals, the advantage of the closed
real system vs. closed ideal system is bounded by the sum. -/
theorem plug_compose [OpenTheory.HasPlugWireFactor T]
    {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ : PortBoundary}
    {real ideal : T.Obj Δ}
    {K_real K_ideal : T.Obj (PortBoundary.swap Δ)}
    (hProt : CompEmulates sem ε₁ real ideal)
    (hEnv : CompEmulates sem ε₂ K_real K_ideal) :
    sem.distAdvantage (T.close real K_real) (T.close ideal K_ideal) ≤ ε₁ + ε₂ := calc
  sem.distAdvantage (T.close real K_real) (T.close ideal K_ideal)
    ≤ sem.distAdvantage (T.close real K_real) (T.close ideal K_real) +
      sem.distAdvantage (T.close ideal K_real) (T.close ideal K_ideal) :=
      sem.distAdvantage_triangle _ _ _
  _ ≤ ε₁ + ε₂ := by
      apply add_le_add
      · exact hProt K_real
      · simp only [OpenTheory.close, OpenTheory.plug_comm ideal]
        exact hEnv ideal

end CompEmulates

/-! ## Simulator-based computational UC security -/

/--
`CompUCSecure sem ε protocol ideal SimSpace simulate` is the
simulator-based UC security statement with bounded advantage.

There exists a simulator parameter `s : SimSpace` such that for every
context `K`, the distinguishing advantage between the real execution
and the simulated ideal execution is at most `ε`.
-/
def CompUCSecure (sem : Semantics T) (ε : ℝ)
    {Δ : PortBoundary}
    (protocol ideal : T.Obj Δ)
    (SimSpace : Type*) (simulate : SimSpace → T.Plug Δ → T.Plug Δ) : Prop :=
  ∃ s : SimSpace, ∀ K : T.Plug Δ,
    sem.distAdvantage (T.close protocol K) (T.close ideal (simulate s K)) ≤ ε

/--
Computational emulation implies simulator-based UC security with the
trivial (identity) simulator.
-/
theorem CompEmulates.toCompUCSecure {sem : Semantics T} {ε : ℝ}
    {Δ : PortBoundary} {protocol ideal : T.Obj Δ}
    (h : CompEmulates sem ε protocol ideal) :
    CompUCSecure sem ε protocol ideal PUnit (fun _ K => K) :=
  ⟨⟨⟩, h⟩

/--
Simulator-based UC security with identity simulation recovers
computational emulation.
-/
theorem CompUCSecure.toCompEmulates_id {sem : Semantics T} {ε : ℝ}
    {Δ : PortBoundary} {protocol ideal : T.Obj Δ}
    (hSec : CompUCSecure sem ε protocol ideal PUnit (fun _ K => K)) :
    CompEmulates sem ε protocol ideal :=
  let ⟨_, h⟩ := hSec; h

/-! ## Asymptotic computational emulation -/

/--
`AsympCompEmulates` is the asymptotic version of computational emulation.

Given a family of theories `T n` indexed by security parameter `n : ℕ`,
with corresponding semantics, real/ideal systems, and adversary-chosen
environments, this asserts that every PPT adversary has negligible
distinguishing advantage.
-/
def AsympCompEmulates
    (T : ℕ → OpenTheory.{u}) (sem : ∀ n, Semantics (T n))
    {Δ : PortBoundary}
    (real ideal : ∀ n, (T n).Obj Δ)
    (Adv : Type*) (isPPT : Adv → Prop)
    (env : Adv → ∀ n, (T n).Plug Δ) : Prop :=
  ∀ A, isPPT A → negligible fun n =>
    ENNReal.ofReal <|
      (sem n).distAdvantage
        ((T n).close (real n) (env A n))
        ((T n).close (ideal n) (env A n))

/--
Pointwise bounded advantage implies asymptotic security: if at each
security parameter the advantage is bounded by `f n`, and `f` is
negligible, then the asymptotic emulation holds (for any adversary class).
-/
theorem AsympCompEmulates.of_pointwise_bound
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    {Δ : PortBoundary}
    {real ideal : ∀ n, (T n).Obj Δ}
    {Adv : Type*} {isPPT : Adv → Prop}
    {env : Adv → ∀ n, (T n).Plug Δ}
    (f : ℕ → ℝ≥0∞) (hf : negligible f)
    (hbound : ∀ (_A : Adv) (n : ℕ) (K : (T n).Plug Δ),
      ENNReal.ofReal ((sem n).distAdvantage
        ((T n).close (real n) K)
        ((T n).close (ideal n) K)) ≤ f n) :
    AsympCompEmulates T sem real ideal Adv isPPT env :=
  fun A _ => negligible_of_le (fun n => hbound A n (env A n)) hf

/--
Convert a family of pointwise `CompEmulates` bounds into an asymptotic
statement when the bound function is negligible.
-/
theorem AsympCompEmulates.of_compEmulates
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    {Δ : PortBoundary}
    {real ideal : ∀ n, (T n).Obj Δ}
    {Adv : Type*} {isPPT : Adv → Prop}
    {env : Adv → ∀ n, (T n).Plug Δ}
    (ε : ℕ → ℝ) (hε : negligible (fun n => ENNReal.ofReal (ε n)))
    (hComp : ∀ n, CompEmulates (sem n) (ε n) (real n) (ideal n)) :
    AsympCompEmulates T sem real ideal Adv isPPT env :=
  fun A _ => negligible_of_le
    (fun n => ENNReal.ofReal_le_ofReal (hComp n (env A n))) hε

/-! ### Asymptotic composition -/

/-- **Asymptotic UC composition for `par`**: if each component's pointwise
advantage is negligible, then the parallel composition also has negligible
advantage. -/
theorem AsympCompEmulates.par_compose
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    [∀ n, OpenTheory.HasPlugWireFactor (T n)]
    {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : ∀ n, (T n).Obj Δ₁}
    {real₂ ideal₂ : ∀ n, (T n).Obj Δ₂}
    {Adv : Type*} {isPPT : Adv → Prop}
    {env : Adv → ∀ n, (T n).Plug (PortBoundary.tensor Δ₁ Δ₂)}
    (ε₁ ε₂ : ℕ → ℝ)
    (hε₁ : negligible (fun n => ENNReal.ofReal (ε₁ n)))
    (hε₂ : negligible (fun n => ENNReal.ofReal (ε₂ n)))
    (h₁ : ∀ n, CompEmulates (sem n) (ε₁ n) (real₁ n) (ideal₁ n))
    (h₂ : ∀ n, CompEmulates (sem n) (ε₂ n) (real₂ n) (ideal₂ n)) :
    AsympCompEmulates T sem
      (fun n => (T n).par (real₁ n) (real₂ n))
      (fun n => (T n).par (ideal₁ n) (ideal₂ n))
      Adv isPPT env :=
  of_compEmulates (fun n => ε₁ n + ε₂ n)
    (negligible_of_le
      (fun _ => ENNReal.ofReal_add_le)
      (negligible_add hε₁ hε₂))
    (fun n => CompEmulates.par_compose (h₁ n) (h₂ n))

/-- **Asymptotic UC composition for `wire`**: if each factor's pointwise
advantage is negligible, then the wired composition also has negligible
advantage. -/
theorem AsympCompEmulates.wire_compose
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    [∀ n, OpenTheory.HasPlugWireFactor (T n)]
    {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ : ∀ n, (T n).Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ :
      ∀ n, (T n).Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    {Adv : Type*} {isPPT : Adv → Prop}
    {env : Adv → ∀ n, (T n).Plug (PortBoundary.tensor Δ₁ Δ₂)}
    (ε₁ ε₂ : ℕ → ℝ)
    (hε₁ : negligible (fun n => ENNReal.ofReal (ε₁ n)))
    (hε₂ : negligible (fun n => ENNReal.ofReal (ε₂ n)))
    (h₁ : ∀ n, CompEmulates (sem n) (ε₁ n) (real₁ n) (ideal₁ n))
    (h₂ : ∀ n, CompEmulates (sem n) (ε₂ n) (real₂ n) (ideal₂ n)) :
    AsympCompEmulates T sem
      (fun n => (T n).wire (real₁ n) (real₂ n))
      (fun n => (T n).wire (ideal₁ n) (ideal₂ n))
      Adv isPPT env :=
  of_compEmulates (fun n => ε₁ n + ε₂ n)
    (negligible_of_le
      (fun _ => ENNReal.ofReal_add_le)
      (negligible_add hε₁ hε₂))
    (fun n => CompEmulates.wire_compose (h₁ n) (h₂ n))

/-- **Asymptotic UC composition for `plug`**: if both the protocol and
the environment have negligible pointwise advantages, then the
distinguishing advantage of the closed real vs. closed ideal system
is negligible. -/
theorem AsympCompEmulates.plug_compose
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    [∀ n, OpenTheory.HasPlugWireFactor (T n)]
    {Δ : PortBoundary}
    {real ideal : ∀ n, (T n).Obj Δ}
    {K_real K_ideal : ∀ n, (T n).Obj (PortBoundary.swap Δ)}
    (ε₁ ε₂ : ℕ → ℝ)
    (hε₁ : negligible (fun n => ENNReal.ofReal (ε₁ n)))
    (hε₂ : negligible (fun n => ENNReal.ofReal (ε₂ n)))
    (hProt : ∀ n, CompEmulates (sem n) (ε₁ n) (real n) (ideal n))
    (hEnv : ∀ n, CompEmulates (sem n) (ε₂ n) (K_real n) (K_ideal n)) :
    negligible fun n =>
      ENNReal.ofReal <|
        (sem n).distAdvantage
          ((T n).close (real n) (K_real n))
          ((T n).close (ideal n) (K_ideal n)) :=
  negligible_of_le
    (fun n => ENNReal.ofReal_le_ofReal
      (CompEmulates.plug_compose (hProt n) (hEnv n)))
    (negligible_of_le
      (fun _ => ENNReal.ofReal_add_le)
      (negligible_add hε₁ hε₂))

/-! ## Bridge to `SecurityGame` -/

/--
The UC distinguishing game: a `SecurityGame` whose advantage at adversary
`A` and security parameter `n` is the total variation distance between
the real and ideal closed executions under the environment chosen by `A`.
-/
noncomputable def ucDistGame
    (T : ℕ → OpenTheory.{u}) (sem : ∀ n, Semantics (T n))
    {Δ : PortBoundary}
    (real ideal : ∀ n, (T n).Obj Δ)
    {Adv : Type*} (env : Adv → ∀ n, (T n).Plug Δ) : SecurityGame Adv where
  advantage A n := ENNReal.ofReal <|
    (sem n).distAdvantage
      ((T n).close (real n) (env A n))
      ((T n).close (ideal n) (env A n))

/--
`AsympCompEmulates` is exactly `secureAgainst isPPT` for the UC
distinguishing game. This is definitional.
-/
theorem AsympCompEmulates.iff_secureAgainst
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    {Δ : PortBoundary}
    {real ideal : ∀ n, (T n).Obj Δ}
    {Adv : Type*} {isPPT : Adv → Prop}
    {env : Adv → ∀ n, (T n).Plug Δ} :
    AsympCompEmulates T sem real ideal Adv isPPT env ↔
      (ucDistGame T sem real ideal env).secureAgainst isPPT :=
  Iff.rfl

/--
If real UC-emulates ideal, then the UC distinguishing game is secure against
any adversary class. Uses the `SecurityGame.secureAgainst` vocabulary.
-/
theorem ucDistGame_secureAgainst_of_asympCompEmulates
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    {Δ : PortBoundary}
    {real ideal : ∀ n, (T n).Obj Δ}
    {Adv : Type*} {isPPT : Adv → Prop}
    {env : Adv → ∀ n, (T n).Plug Δ}
    (h : AsympCompEmulates T sem real ideal Adv isPPT env) :
    (ucDistGame T sem real ideal env).secureAgainst isPPT :=
  h

/--
UC security reduction: if security of `g₁` reduces to UC-emulation of
`real` by `ideal`, then `g₁` is secure whenever UC-emulation holds.

This bridges `SecurityGame.secureAgainst_of_reduction` to the UC setting:
given a reduction from a standard security game to the UC distinguishing
game, UC-emulation implies security of the original game.
-/
theorem SecurityGame.secureAgainst_of_ucEmulation
    {T : ℕ → OpenTheory.{u}} {sem : ∀ n, Semantics (T n)}
    {Δ : PortBoundary}
    {real ideal : ∀ n, (T n).Obj Δ}
    {Adv Adv' : Type*} {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {env : Adv' → ∀ n, (T n).Plug Δ}
    {g : SecurityGame Adv} {reduce : Adv → Adv'}
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hbound : ∀ A n,
      g.advantage A n ≤ (ucDistGame T sem real ideal env).advantage (reduce A) n)
    (hUC : AsympCompEmulates T sem real ideal Adv' isPPT' env) :
    g.secureAgainst isPPT :=
  SecurityGame.secureAgainst_of_reduction hreduce hbound hUC

end UC
end Interaction
