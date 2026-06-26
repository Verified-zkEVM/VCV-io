/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Probability tactic benchmark

A curated corpus of "high-school / intro-crypto-prereq probability" facts, each discharged by `simp`,
`grind`, or `simp; grind`. The file has three jobs:

* **Regression guard.** These are facts the probability automation *should* always solve; if a
  future change breaks one, the build fails here in isolation rather than deep inside a downstream
  proof.
* **Effectiveness benchmark.** Each fact uses the *weakest* standard tactic that closes it,
  preferring `grind` alone, then `simp`, then `simp; grind`; where a fact is closed by *both* `simp`
  and `grind`, both are kept so each tactic stays exercised. The spread is a direct measure of how
  broadly useful the tactics are on probability goals.
* **Aspirational target.** Where a fact needs more guidance than one would hope, it is kept with its
  working proof and a `target(grind)` note, so future tactic work has a concrete goal to simplify.

Concrete facts over `Bool`/`Fin n` are expected to be solved outright; abstract analogues over an
arbitrary `SampleableType` carrier are the harder case (an infinite support removes the grounding
`grind` relies on). `ProbComp` itself never fails — interesting `Pr[⊥ | _]` lives in
`OptionT ProbComp` (the `$`-selection monad), exercised in the failure section.
-/

open OracleComp ProbComp ENNReal

namespace VCVioTest.ProbabilityTactics

/-! ## Single uniform draw

A fair coin and a fair die: every outcome of a uniform draw over an `n`-element type has
probability `1 / n`.

target(grind): `grind` does not solve these — computing a concrete probability needs the
`Fintype.card`/`ℝ≥0∞` arithmetic that `grind` does not do. It now *fails fast* (the
support-quantifier characterizations were made `simp`-only; previously they made `grind` saturate
and time out even on `Bool`). `simp` closes them outright. -/

example : Pr[= true | $ᵗ Bool] = 2⁻¹ := by simp
example : Pr[= false | $ᵗ Bool] = 2⁻¹ := by simp
example : Pr[= (0 : Fin 6) | $ᵗ (Fin 6)] = 6⁻¹ := by simp
example : Pr[= (5 : Fin 6) | $ᵗ (Fin 6)] = 6⁻¹ := by simp

/-! ## Deterministic computations

A `pure` computation puts all of its mass on its value. Both `simp` and `grind` close these. -/

example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] = 1 := by grind

example (x y : Bool) : Pr[= x | (pure y : ProbComp Bool)] = if x = y then 1 else 0 := by simp
example (x y : Bool) : Pr[= x | (pure y : ProbComp Bool)] = if x = y then 1 else 0 := by grind

/-! ## Never-failing draws

A bare `ProbComp` computation never fails: `Pr[⊥ | _] = 0`, even after many steps. -/

example : Pr[⊥ | $ᵗ Bool] = 0 := by simp
example : Pr[⊥ | $ᵗ (Fin 6)] = 0 := by simp
example : Pr[⊥ | do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x && y)] = 0 := by simp

/-! ## Support of basic computations

The support of a uniform draw is everything; the support of a `pure` is a singleton. Membership and
singleton-support facts are closed by both `simp` and `grind`. -/

example : support ($ᵗ Bool) = Set.univ := by simp
example : finSupport ($ᵗ (Fin 6)) = Finset.univ := by simp

example (x : Bool) : x ∈ support ($ᵗ Bool) := by simp
example (x : Bool) : x ∈ support ($ᵗ Bool) := by grind

example (x : Bool) : support (pure x : ProbComp Bool) = {x} := by simp
example (x : Bool) : support (pure x : ProbComp Bool) = {x} := by grind

/-! ## Complement and the addition rule

`Pr[¬p] = 1 - Pr[p]` for a non-failing computation, and the probability of a union of disjoint
outcomes adds up.

target(grind): as with the single-draw section, `grind` fails fast on a concrete event probability
(it lacks the count/arithmetic); `simp` evaluates it. -/

example : Pr[fun b => b ≠ true | $ᵗ Bool] = 2⁻¹ := by simp

-- target(grind): the favorable/total count needs `congr 1` to discharge the `Finset.card` after the
-- `probEvent_uniformSample` rewrite; ideally `grind` evaluates the finite count itself.
example : Pr[fun n => n = 0 ∨ n = 1 | $ᵗ (Fin 6)] = 2 / 6 := by
  simp; congr 1

/-! ## Independence and the multiplication rule

Two independent uniform draws factor: the joint mass is the product of the marginals. "At least one
head" in two fair coins is `3/4`. -/

example (a b : Bool) :
    Pr[= (a, b) | do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x, y)]
      = Pr[= a | $ᵗ Bool] * Pr[= b | $ᵗ Bool] := by simp

example :
    Pr[= ((5 : Fin 6), (5 : Fin 6)) | do let x ← $ᵗ (Fin 6); let y ← $ᵗ (Fin 6); pure (x, y)]
      = 6⁻¹ * 6⁻¹ := by simp

example : Pr[fun p => p.1 = true ∨ p.2 = true | $ᵗ (Bool × Bool)] = 3 / 4 := by simp; congr 1

/-! ## Symmetry, bounds, and monotonicity

Every outcome of a uniform draw is equally likely (closed by both `simp` and `grind`); probabilities
are bounded by one and respect implication between events. -/

example (x y : Fin 6) : Pr[= x | $ᵗ (Fin 6)] = Pr[= y | $ᵗ (Fin 6)] := by simp
example (x y : Fin 6) : Pr[= x | $ᵗ (Fin 6)] = Pr[= y | $ᵗ (Fin 6)] := by grind

example (mx : ProbComp Bool) (p : Bool → Prop) : Pr[p | mx] ≤ 1 := by simp

example (mx : ProbComp Bool) (p q : Bool → Prop) (h : ∀ x, p x → q x) :
    Pr[p | mx] ≤ Pr[q | mx] := probEvent_mono'' h

/-! ## Bind and map pushforwards

Mapping a draw through a function pushes the distribution forward along that function. -/

example : support (do let b ← $ᵗ Bool; pure (!b)) = Set.univ := by
  ext b; cases b <;> simp

example (mx : ProbComp Bool) (f : Bool → Fin 6) (q : Fin 6 → Prop) :
    Pr[q | f <$> mx] = Pr[q ∘ f | mx] := by simp

/-! ## The shape of `do`: nesting, branching, patterns, and many steps

The probability automation should see through the full surface syntax of `do`-notation: a pure
`let :=`, nested `do` blocks, pattern-matching binds, `if`/`then`/`else`, and long chains. None of
these computations can fail, so each has `Pr[⊥ | _] = 0` and full support. -/

/-- A pure `let :=` step inside `do`. -/
def coinThenNeg : ProbComp Bool := do
  let x ← $ᵗ Bool
  let y := !x
  pure y

/-- A pattern-matching bind over a nested product draw. -/
def twoThenAnd : ProbComp Bool := do
  let (a, b) ← (do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x, y))
  pure (a && b)

/-- A nested `do` block whose result feeds the outer one. -/
def nestedDraw : ProbComp Bool := do
  let x ← $ᵗ Bool
  let y ← (do let z ← $ᵗ Bool; pure (x && z))
  pure y

/-- An `if`/`then`/`else` branch on a coin. -/
def branchToFin : ProbComp (Fin 2) := do
  let b ← $ᵗ Bool
  if b then pure 0 else pure 1

/-- A five-step chain of independent coins. -/
def fiveCoins : ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool; let e ← $ᵗ Bool
  pure (a && b && c && d && e)

example : Pr[⊥ | coinThenNeg] = 0 := by simp [coinThenNeg]
example : Pr[⊥ | twoThenAnd] = 0 := by simp [twoThenAnd]
example : Pr[⊥ | nestedDraw] = 0 := by simp [nestedDraw]
example : Pr[⊥ | branchToFin] = 0 := by simp [branchToFin]
example : Pr[⊥ | fiveCoins] = 0 := by simp [fiveCoins]

example : support coinThenNeg = Set.univ := by
  ext b; cases b <;> simp [coinThenNeg]

example : Pr[= false | coinThenNeg] = Pr[= true | $ᵗ Bool] := by simp [coinThenNeg]

/-! ## Failing computations and the `Set.Nonempty` bridge

In `OptionT ProbComp`, sampling can fail. Selecting from the empty list fails with probability one;
selecting from a nonempty list never fails. `grind` reasons about `Pr[⊥ | _] = 1` through the
`Set.Nonempty` bridge `probFailure_eq_one_iff_not_nonempty` (it keeps `Set.Nonempty` atomic, so this
does not re-trigger the support-quantifier saturation). -/

example : Pr[⊥ | ($ ([] : List Bool) : OptionT ProbComp Bool)] = 1 := by simp
example : Pr[⊥ | ($ ([true, false] : List Bool) : OptionT ProbComp Bool)] = 0 := by simp

/-- Abort unless the coin comes up `true`: fails with probability one half. -/
def abortOnFalse : OptionT ProbComp Bool := do
  let b ← $ᵗ Bool
  if b then pure true else failure

example : Pr[⊥ | abortOnFalse] = 2⁻¹ := by
  simp [abortOnFalse, probFailure_bind_eq_add_tsum]

-- A computation with nonempty support does not fail with probability one — `grind` via the bridge.
example (mx : OptionT ProbComp Bool) (h : (support mx).Nonempty) : Pr[⊥ | mx] ≠ 1 := by grind
example (mx : ProbComp Bool) (h : (support mx).Nonempty) : Pr[⊥ | mx] ≠ 1 := by grind

/-! ## Cryptography prerequisites

The kind of facts an intro-to-cryptography course assumes: guessing a uniform secret, one-time-pad
secrecy, and collision probability. -/

-- Guessing a uniform secret of `Fin 6` succeeds with probability `1/6`.
example (guess : Fin 6) : Pr[= guess | $ᵗ (Fin 6)] = 6⁻¹ := by simp

-- One-time pad secrecy: adding a uniform key makes the ciphertext distribution independent of the
-- message (here over `ZMod 2`, i.e. a one-bit XOR pad).
example (msg : ZMod 2) : 𝒟[(msg + ·) <$> ($ᵗ (ZMod 2))] = 𝒟[$ᵗ (ZMod 2)] := by
  simp only [evalDist_add_left_uniform]

-- Collision: two independent fair dice agree with probability `1/6`.
example : Pr[fun p => p.1 = p.2 | $ᵗ (Fin 6 × Fin 6)] = 6 / 36 := by simp; congr 1

-- Normalization: the outcome probabilities of a fair die sum to one.
example : ∑ k : Fin 6, Pr[= k | $ᵗ (Fin 6)] = 1 := sum_probOutput_eq_one (by simp)

/-! ## Abstract carriers

The same facts over an arbitrary `SampleableType` carrier. `grind` cannot factor the applicative
product `(·, ·) <$> _ <*> _` (the second factor sits under `Seq.seq`'s `Unit → _` thunk, which its
pattern matcher cannot index), and the bind/`tsum` expansion over an infinite carrier does not
terminate; the idiom is to `simp` the structure away first, then let `grind` finish. -/

section abstract
variable (α β : Type) [SampleableType α] [SampleableType β]

example (x y : α) : Pr[= x | $ᵗ α] = Pr[= y | $ᵗ α] := by grind

example : support ($ᵗ α) = Set.univ := by simp

example : Pr[⊥ | $ᵗ α] = 0 := by simp

example : (support ($ᵗ α)).Nonempty := by grind

example : Pr[⊥ | $ᵗ α] ≠ 1 := by grind

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
