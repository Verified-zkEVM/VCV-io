/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.Emulates
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.Asymptotics.Negligible
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Computational observation layer for UC security

This file bridges the abstract UC judgments (`Emulates`, `UCSecure`) to
concrete computational indistinguishability by instantiating the `ObsEq`
parameter with distributional advantage bounds.

## Main definitions

* `Semantics T` is a function extracting a `ProbComp Unit` game from each
  closed system in the theory `T`. This is the minimal bridge between the
  structural open-composition layer and the probabilistic crypto layer.

* `CompEmulates sem ε real ideal` asserts that for every environment (plug),
  the distinguishing advantage between the real and ideal closed systems
  is at most `ε`.

* `AsympCompEmulates` is the asymptotic variant: for every PPT adversary
  choosing environments, the advantage is negligible in the security
  parameter.

* `CompUCSecure sem ε protocol ideal SimSpace simulate` is the
  simulator-based variant with bounded advantage.

## Main results

* `CompEmulates.refl`: advantage zero against itself.
* `CompEmulates.triangle`: transitivity with additive advantage bounds.
* `CompEmulates.map_invariance`: boundary adaptation preserves the bound.
* `CompEmulates.par_compose`, `wire_compose`, `plug_compose`:
  advantages add under parallel, wired, and plugged composition.
* `CompEmulates.toEmulates`: every `CompEmulates` yields an abstract
  `Emulates` for the induced observation relation.
* `CompUCSecure.toCompEmulates`: simulator-based security implies
  computational emulation when the simulator is the identity.
* `AsympCompEmulates.par_compose`, `wire_compose`, `plug_compose`:
  asymptotic composition from pointwise negligible bounds.
* `ucDistGame`: constructs the `SecurityGame` whose advantage is the
  UC distinguishing advantage.
* `AsympCompEmulates.iff_secureAgainst`: `AsympCompEmulates` is
  equivalent to security of the UC distinguishing game.
-/

universe u

open OracleComp ProbComp ENNReal

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/--
`Semantics T` extracts a probabilistic game (`ProbComp Unit`) from each
closed system in the open-composition theory `T`.

The `Unit` return type matches the convention used by
`ProbComp.distAdvantage`: success is `()` and failure is `⊥`.
This is the minimal bridge needed to give computational meaning to the
abstract `Emulates` judgment.
-/
structure Semantics (T : OpenTheory.{u}) where
  run : T.Closed → ProbComp Unit

/--
`CompEmulates sem ε real ideal` asserts that `real` computationally
emulates `ideal` up to advantage `ε` under semantics `sem`.

For every plug `K : T.Plug Δ`, the distinguishing advantage between the
real-world and ideal-world closed executions is at most `ε`.
-/
def CompEmulates (sem : Semantics T) (ε : ℝ)
    {Δ : PortBoundary} (real ideal : T.Obj Δ) : Prop :=
  ∀ K : T.Plug Δ,
    (sem.run (T.close real K)).distAdvantage (sem.run (T.close ideal K)) ≤ ε

/--
The observation relation on closed systems induced by a semantics and
an advantage bound: two closed systems are related when their
distinguishing advantage is at most `ε`.
-/
def compObsEq (sem : Semantics T) (ε : ℝ) : T.Closed → T.Closed → Prop :=
  fun c₁ c₂ => (sem.run c₁).distAdvantage (sem.run c₂) ≤ ε

namespace CompEmulates

/--
`CompEmulates` is an instance of abstract `Emulates` for the observation
relation `compObsEq sem ε`.
-/
theorem toEmulates {sem : Semantics T} {ε : ℝ}
    {Δ : PortBoundary} {real ideal : T.Obj Δ}
    (h : CompEmulates sem ε real ideal) :
    Emulates real ideal (compObsEq sem ε) :=
  ⟨h⟩

/--
Every system computationally emulates itself with advantage zero.
-/
theorem refl (sem : Semantics T) {Δ : PortBoundary} (W : T.Obj Δ) :
    CompEmulates sem 0 W W :=
  fun K => by simp [ProbComp.distAdvantage_self]

/--
Computational emulation composes transitively with additive advantage
bounds (triangle inequality on distinguishing advantage).
-/
theorem triangle {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ : PortBoundary} {W₁ W₂ W₃ : T.Obj Δ}
    (h₁₂ : CompEmulates sem ε₁ W₁ W₂)
    (h₂₃ : CompEmulates sem ε₂ W₂ W₃) :
    CompEmulates sem (ε₁ + ε₂) W₁ W₃ :=
  fun K => calc
    (sem.run (T.close W₁ K)).distAdvantage (sem.run (T.close W₃ K))
      ≤ (sem.run (T.close W₁ K)).distAdvantage (sem.run (T.close W₂ K)) +
        (sem.run (T.close W₂ K)).distAdvantage (sem.run (T.close W₃ K)) :=
          ProbComp.distAdvantage_triangle _ _ _
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
theorem par_left [OpenTheory.CompactClosed T]
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
theorem par_right [OpenTheory.CompactClosed T]
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
theorem par_compose [OpenTheory.CompactClosed T]
    {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : T.Obj Δ₁} {real₂ ideal₂ : T.Obj Δ₂}
    (h₁ : CompEmulates sem ε₁ real₁ ideal₁)
    (h₂ : CompEmulates sem ε₂ real₂ ideal₂) :
    CompEmulates sem (ε₁ + ε₂) (T.par real₁ real₂) (T.par ideal₁ ideal₂) :=
  triangle (par_left h₁ real₂) (par_right ideal₁ h₂)

/-- Replacing the left factor of a wiring preserves the computational
emulation bound. -/
theorem wire_left [OpenTheory.CompactClosed T]
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
theorem wire_right [OpenTheory.CompactClosed T]
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
theorem wire_compose [OpenTheory.CompactClosed T]
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
theorem plug_compose [OpenTheory.CompactClosed T]
    {sem : Semantics T} {ε₁ ε₂ : ℝ}
    {Δ : PortBoundary}
    {real ideal : T.Obj Δ}
    {K_real K_ideal : T.Obj (PortBoundary.swap Δ)}
    (hProt : CompEmulates sem ε₁ real ideal)
    (hEnv : CompEmulates sem ε₂ K_real K_ideal) :
    (sem.run (T.close real K_real)).distAdvantage
      (sem.run (T.close ideal K_ideal)) ≤ ε₁ + ε₂ := calc
  (sem.run (T.close real K_real)).distAdvantage
      (sem.run (T.close ideal K_ideal))
    ≤ (sem.run (T.close real K_real)).distAdvantage
        (sem.run (T.close ideal K_real)) +
      (sem.run (T.close ideal K_real)).distAdvantage
        (sem.run (T.close ideal K_ideal)) :=
      ProbComp.distAdvantage_triangle _ _ _
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
    (sem.run (T.close protocol K)).distAdvantage
      (sem.run (T.close ideal (simulate s K))) ≤ ε

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
      ProbComp.distAdvantage
        ((sem n).run ((T n).close (real n) (env A n)))
        ((sem n).run ((T n).close (ideal n) (env A n)))

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
      ENNReal.ofReal (ProbComp.distAdvantage
        ((sem n).run ((T n).close (real n) K))
        ((sem n).run ((T n).close (ideal n) K))) ≤ f n) :
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
    [∀ n, OpenTheory.CompactClosed (T n)]
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
    [∀ n, OpenTheory.CompactClosed (T n)]
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
    [∀ n, OpenTheory.CompactClosed (T n)]
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
        ProbComp.distAdvantage
          ((sem n).run ((T n).close (real n) (K_real n)))
          ((sem n).run ((T n).close (ideal n) (K_ideal n))) :=
  negligible_of_le
    (fun n => ENNReal.ofReal_le_ofReal
      (CompEmulates.plug_compose (hProt n) (hEnv n)))
    (negligible_of_le
      (fun _ => ENNReal.ofReal_add_le)
      (negligible_add hε₁ hε₂))

/-! ## Bridge to `SecurityGame` -/

/--
The UC distinguishing game: a `SecurityGame` whose advantage at adversary
`A` and security parameter `n` is the distributional distance between the
real and ideal closed executions under the environment chosen by `A`.
-/
noncomputable def ucDistGame
    (T : ℕ → OpenTheory.{u}) (sem : ∀ n, Semantics (T n))
    {Δ : PortBoundary}
    (real ideal : ∀ n, (T n).Obj Δ)
    {Adv : Type*} (env : Adv → ∀ n, (T n).Plug Δ) : SecurityGame Adv where
  advantage A n := ENNReal.ofReal <|
    ProbComp.distAdvantage
      ((sem n).run ((T n).close (real n) (env A n)))
      ((sem n).run ((T n).close (ideal n) (env A n)))

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
