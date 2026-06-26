/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Probability tactic benchmark

A curated corpus of "high-school probability" facts, each discharged by `simp`, `grind`, or
`simp; grind`. The file has three jobs:

* **Regression guard.** These are facts the probability automation *should* always solve; if a
  future change breaks one, the build fails here in isolation rather than deep inside a downstream
  proof.
* **Effectiveness benchmark.** Each fact uses the *weakest* standard tactic that closes it,
  preferring `grind` alone, then `simp`, then `simp; grind`. The spread is a direct measure of how
  broadly useful the tactics are on probability goals.
* **Aspirational target.** Where a fact needs more guidance than one would hope, it is kept with its
  working proof and a `target(grind)` note, so future tactic work has a concrete goal to simplify.

The corpus is split into concrete facts over `Bool`/`Fin n` (which the tactics are expected to solve
outright), abstract analogues over arbitrary `SampleableType` carriers (the harder case — an
infinite support removes the grounding `grind` relies on), and a few sentinels mirroring shapes used
throughout the library.
-/

open OracleComp ProbComp ENNReal

namespace VCVioTest.ProbabilityTactics

/-! ## Single uniform draw

A fair coin and a fair die: every outcome of a uniform draw over an `n`-element type has
probability `1 / n`.

target(grind): `grind` does not currently solve these — computing a concrete uniform probability
forces it through `probOutput → support → card`, which pulls in the `∃/∀ x ∈ support` /
`support = {x}` characterizations and saturates (it times out even on `Bool`). `simp` closes them
outright. -/

example : Pr[= true | $ᵗ Bool] = 2⁻¹ := by simp

example : Pr[= false | $ᵗ Bool] = 2⁻¹ := by simp

example : Pr[= (0 : Fin 6) | $ᵗ (Fin 6)] = 6⁻¹ := by simp

example : Pr[= (5 : Fin 6) | $ᵗ (Fin 6)] = 6⁻¹ := by simp

/-! ## Deterministic computations and never-failing draws

A `pure` computation puts all of its mass on its value; a uniform draw never fails. -/

example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] = 1 := by grind

example (x y : Bool) : Pr[= x | (pure y : ProbComp Bool)] = if x = y then 1 else 0 := by grind

example : Pr[⊥ | $ᵗ Bool] = 0 := by simp

example : Pr[⊥ | $ᵗ (Fin 6)] = 0 := by simp

/-! ## Support of basic computations

The support of a uniform draw is everything; the support of a `pure` is a singleton. -/

example : support ($ᵗ Bool) = Set.univ := by simp

example (x : Bool) : x ∈ support ($ᵗ Bool) := by grind

example : finSupport ($ᵗ (Fin 6)) = Finset.univ := by simp

example (x : Bool) : support (pure x : ProbComp Bool) = {x} := by grind

/-! ## Complement and the addition rule

`Pr[¬p] = 1 - Pr[p]` for a non-failing computation, and the probability of a union of disjoint
outcomes adds up.

target(grind): as with the single-draw section, `grind` saturates on a concrete event probability;
`simp` evaluates the count. -/

example : Pr[fun b => b ≠ true | $ᵗ Bool] = 2⁻¹ := by simp

-- target(grind): the favorable/total count needs `congr 1` to discharge the `Finset.card` after the
-- `probEvent_uniformSample` rewrite; ideally `grind` evaluates the finite count itself.
example : Pr[fun n => n = 0 ∨ n = 1 | $ᵗ (Fin 6)] = 2 / 6 := by
  simp; congr 1

/-! ## Independence and the multiplication rule

Two independent uniform draws factor: the joint mass is the product of the marginals. -/

example (a b : Bool) :
    Pr[= (a, b) | do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x, y)]
      = Pr[= a | $ᵗ Bool] * Pr[= b | $ᵗ Bool] := by simp

example :
    Pr[= ((5 : Fin 6), (5 : Fin 6)) | do let x ← $ᵗ (Fin 6); let y ← $ᵗ (Fin 6); pure (x, y)]
      = 6⁻¹ * 6⁻¹ := by simp

/-! ## Symmetry, bounds, and monotonicity

Every outcome of a uniform draw is equally likely; probabilities are bounded by one and respect
implication between events. -/

example (x y : Fin 6) : Pr[= x | $ᵗ (Fin 6)] = Pr[= y | $ᵗ (Fin 6)] := by grind

example (mx : ProbComp Bool) (p : Bool → Prop) : Pr[p | mx] ≤ 1 := by simp

example (mx : ProbComp Bool) (p q : Bool → Prop) (h : ∀ x, p x → q x) :
    Pr[p | mx] ≤ Pr[q | mx] := by
  exact probEvent_mono'' h

/-! ## Bind and map pushforwards

Mapping a draw through a function pushes the distribution forward along that function. -/

example : support (do let b ← $ᵗ Bool; pure (!b)) = Set.univ := by
  ext b; cases b <;> simp

example (mx : ProbComp Bool) (f : Bool → Fin 6) (q : Fin 6 → Prop) :
    Pr[q | f <$> mx] = Pr[q ∘ f | mx] := by simp

/-! ## Abstract carriers

The same facts over an arbitrary `SampleableType` carrier. Here the support is infinite, so the
`∃/∀ x ∈ support` characterizations have nothing to ground on and `grind` cannot brute-force the
distribution; the idiom is to `simp` the structure away first, then let `grind` finish. -/

section abstract
variable (α β : Type) [SampleableType α] [SampleableType β]

example (x y : α) : Pr[= x | $ᵗ α] = Pr[= y | $ᵗ α] := by grind

example : support ($ᵗ α) = Set.univ := by simp

-- target(simp): the concrete `Pr[⊥ | $ᵗ Bool] = 0` is closed by `simp`, but abstractly `simp` makes
-- no progress; `probFailure_uniformSample` is the direct lemma and is not `@[simp]`.
example : Pr[⊥ | $ᵗ α] = 0 := probFailure_uniformSample α

example (z : α × β) :
    Pr[= z | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] = Pr[= z.1 | $ᵗ α] * Pr[= z.2 | $ᵗ β] := by simp

-- target(grind): the equiprobability of a uniform product. `grind` alone does not terminate here
-- (the applicative product cannot be factored by `grind`, and the infinite support removes any
-- grounding); `simp` factors the product, then `grind` closes the equal-factor goal.
example (x y : α × β) :
    Pr[= x | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] = Pr[= y | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] := by
  simp only [probOutput_seq_map_prod_mk_eq_mul]; grind

end abstract

/-! ## Library-shape sentinels

Small facts in the shape of `grind`-discharged goals used throughout the library, to catch silent
regressions of the probability `grind` set in isolation. -/

example (α : Type) [SampleableType α] (x : α) : x ∈ support ($ᵗ α) := by grind

example (x : Bool) : x ∈ finSupport ($ᵗ Bool) := by grind

example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] = 0 ↔ x ∉ support mx := by grind

end VCVioTest.ProbabilityTactics
