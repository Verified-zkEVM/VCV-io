/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio

/-!
# Probability tactic benchmark

A curated, deliberately broad corpus of "high-school / intro-crypto-prerequisite" facts about
**outcome probabilities, event probabilities, failure probabilities, support, and evaluation
distributions**, each discharged by a single *terminal* tactic — `simp` or `grind`. The file
**gates `simp` and `grind` as stable terminal tactics** over this surface, so a regression in
either surfaces here in isolation rather than deep inside a downstream proof.

Conventions (the full rules are in `CONTRIBUTING.md`, *Tactic Gate Files*):
* **Mirrors.** Where a fact is closed by *both* `simp` and `grind`, both are kept, so each tactic
  stays exercised on that shape. This is the bulk of the file.
* **Gap pairs.** Where only one tactic closes a goal, the entry is a *gap pair*: a
  `fail_if_success (tac; done)` guard on its own line, then the working closer, with a dated
  `gap(tac, date): reason` comment. The guard errors the moment the set improves, so the PR that
  closes a gap retires the guard. One guard covers a family of same-shaped entries when the
  family is named in the section note.
* **One terminal call.** A `;`/multi-line script appears only as the closer of a gap pair.
* **Only stable tactics.** No example hangs or explodes. `grind` reasons well about symbolic /
  atomic / membership / equiprobability / `pure`+`bind`-normalised goals; computing a concrete value
  or factoring a structured computation (`<*>`, a non-trivial `<$>`/`if`) is `simp`'s job.

`grind` normalises monadic structure (`bind_pure`, `pure_bind`, `bind_assoc`, `map_pure` are
`@[grind =]`), so `bind`-`pure`-shaped goals close by `grind`; `Set.Nonempty` bridges
(`probFailure_eq_one_iff_not_nonempty`, `support_uniformSample_nonempty`) keep `Pr[⊥]=1` reasoning
reachable. `ProbComp` itself never fails — interesting `Pr[⊥ | _]` lives in `OptionT ProbComp`.
-/

@[expose] public section

open OracleComp ProbComp ENNReal

namespace VCVioTest.ProbabilityTactics

/-! # 1. Outcome probability — `Pr[= x | _]` -/

/-! ## Deterministic outcomes
A `pure` computation puts all of its mass on its value. -/

example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] = 1 := by grind

example (x y : Bool) : Pr[= x | (pure y : ProbComp Bool)] = if x = y then 1 else 0 := by simp
example (x y : Bool) : Pr[= x | (pure y : ProbComp Bool)] = if x = y then 1 else 0 := by grind

example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] ≠ 0 := by simp
example (x : Bool) : Pr[= x | (pure x : ProbComp Bool)] ≠ 0 := by grind

/-! ## Uniform draws
Every outcome of a uniform draw over an `n`-element type has probability `1 / n`.

gap(grind): computing a concrete value needs `Fintype.card`/`ℝ≥0∞` arithmetic `grind` does not do
(it fails fast); `simp` evaluates it. The first entry carries the guard for the family. Symbolic
facts (`≠ 0`, equiprobability) close by both. -/

example : Pr[= true | $ᵗ Bool] = 2⁻¹ := by
  fail_if_success grind  -- gap(grind, 2026-09-03): concrete values, covers this section
  simp
example : Pr[= (0 : Fin 6) | $ᵗ (Fin 6)] = 6⁻¹ := by simp

example : Pr[= true | $ᵗ Bool] ≠ 0 := by simp
example : Pr[= true | $ᵗ Bool] ≠ 0 := by grind

example (x y : Fin 6) : Pr[= x | $ᵗ (Fin 6)] = Pr[= y | $ᵗ (Fin 6)] := by simp
example (x y : Fin 6) : Pr[= x | $ᵗ (Fin 6)] = Pr[= y | $ᵗ (Fin 6)] := by grind

example : Pr[= true | $ᵗ Bool] = Pr[= false | $ᵗ Bool] := by simp
example : Pr[= true | $ᵗ Bool] = Pr[= false | $ᵗ Bool] := by grind

example : Pr[= (3 : ZMod 5) | $ᵗ (ZMod 5)] = 5⁻¹ := by simp
example : Pr[= (0 : BitVec 4) | $ᵗ (BitVec 4)] = 16⁻¹ := by simp

example : Pr[= (0 : Fin 3) | $ᵗ (Fin 3)] ≠ 0 := by simp
example : Pr[= (0 : Fin 3) | $ᵗ (Fin 3)] ≠ 0 := by grind

example (x : Bool ⊕ Bool) : Pr[= x | $ᵗ (Bool ⊕ Bool)] ≠ 0 := by simp
example (x : Bool ⊕ Bool) : Pr[= x | $ᵗ (Bool ⊕ Bool)] ≠ 0 := by grind

/-! ## Bounds
An outcome probability lies in `[0, 1]` and is never `⊤`.

gap(grind): `0 ≤ _` in `ℝ≥0∞` is just `zero_le`, but `grind` routes through the support machinery
and fails; `simp` closes it. -/

example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] ≤ 1 := by simp
example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] ≤ 1 := by grind

example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] ≠ ⊤ := by simp
example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] ≠ ⊤ := by grind

example (mx : ProbComp Bool) (x : Bool) : 0 ≤ Pr[= x | mx] := by
  fail_if_success grind  -- gap(grind, 2026-09-03): `zero_le` behind the support machinery
  simp

/-! ## `bind`/`pure`-normalised computations
`grind` normalises monadic structure, so a redundant `bind`/`pure` collapses and the outcome
probability matches the underlying draw. -/

example : Pr[= true | do let b ← $ᵗ Bool; pure b] = Pr[= true | $ᵗ Bool] := by simp
example : Pr[= true | do let b ← $ᵗ Bool; pure b] = Pr[= true | $ᵗ Bool] := by grind

example (mx : ProbComp Bool) (x : Bool) :
    Pr[= x | do let y ← mx; pure y] = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) (x : Bool) :
    Pr[= x | do let y ← mx; pure y] = Pr[= x | mx] := by grind

example (x : Bool) : Pr[= x | (do let _ ← $ᵗ Bool; pure x : ProbComp Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (do let _ ← $ᵗ Bool; pure x : ProbComp Bool)] = 1 := by grind

/-! ## Independence and the multiplication rule
Two independent uniform draws factor: the joint mass is the product of the marginals.

The applicative (`<$> … <*>`) spelling factors under `grind` via the `@[grind norm]` rule
`probOutput_seq_map_prod_mk_eq_mul` (the `Seq.seq` thunk is unindexable for E-matching, but
`grind`'s normalization phase handles it).

gap(grind): the `bind`-spelled product — the second draw sits under `bind`'s continuation, which
neither E-matching nor the seq-keyed norm rule reaches; `simp` factors it. The first entry carries
the guard. -/

example (a b : Bool) :
    Pr[= (a, b) | do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x, y)]
      = Pr[= a | $ᵗ Bool] * Pr[= b | $ᵗ Bool] := by
  fail_if_success grind  -- gap(grind, 2026-09-03): bind-spelled product, covers this section
  simp

example :
    Pr[= ((5 : Fin 6), (5 : Fin 6)) | do let x ← $ᵗ (Fin 6); let y ← $ᵗ (Fin 6); pure (x, y)]
      = 6⁻¹ * 6⁻¹ := by simp

example (z : Bool × Bool) :
    Pr[= z | (·, ·) <$> ($ᵗ Bool) <*> ($ᵗ Bool)]
      = Pr[= z.1 | $ᵗ Bool] * Pr[= z.2 | $ᵗ Bool] := by simp
example (z : Bool × Bool) :
    Pr[= z | (·, ·) <$> ($ᵗ Bool) <*> ($ᵗ Bool)]
      = Pr[= z.1 | $ᵗ Bool] * Pr[= z.2 | $ᵗ Bool] := by grind

/-! # 2. Event probability — `Pr[ p | _]` -/

/-! ## Bounds
A probability is at most one and never `⊤`. -/

example (mx : ProbComp Bool) (p : Bool → Prop) : Pr[p | mx] ≤ 1 := by simp
example (mx : ProbComp Bool) (p : Bool → Prop) : Pr[p | mx] ≤ 1 := by grind

example (mx : ProbComp Bool) (p : Bool → Prop) : Pr[p | mx] ≠ ⊤ := by simp
example (mx : ProbComp Bool) (p : Bool → Prop) : Pr[p | mx] ≠ ⊤ := by grind

-- The impossible event has probability zero; a single fair outcome has probability one half.
example (mx : ProbComp Bool) : Pr[fun _ => False | mx] = 0 := by simp
example (mx : ProbComp Bool) : Pr[fun _ => False | mx] = 0 := by grind
example : Pr[fun b => b = true | $ᵗ Bool] = 2⁻¹ := by simp
example : Pr[fun n => n < 3 | $ᵗ (Fin 6)] = 3 / 6 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): the filter card is not evaluated
  fail_if_success grind  -- gap(grind, 2026-09-03): counting
  simp; rfl

/-! ## Monotonicity and complement
An event implies a wider event; the complement subtracts from one. -/

example (mx : ProbComp Bool) (p q : Bool → Prop) (h : ∀ x, p x → q x) :
    Pr[p | mx] ≤ Pr[q | mx] := probEvent_mono'' h

example : Pr[fun b => b ≠ true | $ᵗ Bool] = 2⁻¹ := by simp  -- concrete value, see §uniform draws

/-! ## Counting (favourable / total)
gap: the favourable count over a concrete finite type is left as `↑{…}.card / n`; `rfl`/`congr`
evaluates it afterwards, `simp +decide` does not, and `grind` fails. -/

example : Pr[fun n => n = 0 ∨ n = 1 | $ᵗ (Fin 6)] = 2 / 6 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): the filter card is not evaluated
  fail_if_success grind  -- gap(grind, 2026-09-03): counting
  simp; rfl
example : Pr[fun p => p.1 = true ∨ p.2 = true | $ᵗ (Bool × Bool)] = 3 / 4 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): the filter card is not evaluated
  fail_if_success grind  -- gap(grind, 2026-09-03): counting
  simp; congr 1

/-! ## Map pushforward
The event-probability of a map is the pulled-back event. -/

example (mx : ProbComp Bool) (q : Fin 6 → Prop) (f : Bool → Fin 6) :
    Pr[q | f <$> mx] = Pr[q ∘ f | mx] := by simp
example (mx : ProbComp Bool) (q : Fin 6 → Prop) (f : Bool → Fin 6) :
    Pr[q | f <$> mx] = Pr[q ∘ f | mx] := by grind

/-! # 3. Failure probability — `Pr[⊥ | _]` -/

/-! ## `ProbComp` never fails
A bare `ProbComp` computation — `pure`, a uniform draw, or any `bind` of them — fails with
probability zero. -/

example (x : Bool) : Pr[⊥ | (pure x : ProbComp Bool)] = 0 := by simp
example (x : Bool) : Pr[⊥ | (pure x : ProbComp Bool)] = 0 := by grind

example : Pr[⊥ | $ᵗ Bool] = 0 := by simp
example : Pr[⊥ | $ᵗ Bool] = 0 := by grind

example : Pr[⊥ | do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x && y)] = 0 := by simp
example : Pr[⊥ | do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x && y)] = 0 := by grind

example (α : Type) [SampleableType α] : Pr[⊥ | $ᵗ α] = 0 := by simp
example (α : Type) [SampleableType α] : Pr[⊥ | $ᵗ α] = 0 := by grind

/-! ## Selection and abort (`OptionT ProbComp`)
Selecting from the empty list fails with probability one; from a nonempty list it never fails. A
nonempty support means the computation does not certainly fail (`grind` via the `Set.Nonempty`
bridge). -/

example : Pr[⊥ | ($ ([] : List Bool) : OptionT ProbComp Bool)] = 1 := by simp
example : Pr[⊥ | ($ ([] : List Bool) : OptionT ProbComp Bool)] = 1 := by grind

example : Pr[⊥ | (failure : OptionT ProbComp Bool)] = 1 := by simp
example : Pr[⊥ | (failure : OptionT ProbComp Bool)] = 1 := by grind

example : Pr[⊥ | ($ ([true, false] : List Bool) : OptionT ProbComp Bool)] = 0 := by simp
example : Pr[⊥ | ($ ([true, false] : List Bool) : OptionT ProbComp Bool)] = 0 := by grind

example (mx : OptionT ProbComp Bool) (h : (support mx).Nonempty) : Pr[⊥ | mx] ≠ 1 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): stops at `¬support mx = ∅`
  grind
example (mx : ProbComp Bool) : Pr[⊥ | mx] ≠ 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-03): `≠ 1` from `Pr[⊥] = 0` needs `0 ≠ 1` in `ℝ≥0∞`
  simp

example (α : Type) [SampleableType α] : Pr[⊥ | $ᵗ α] ≠ 1 := by simp
example (α : Type) [SampleableType α] : Pr[⊥ | $ᵗ α] ≠ 1 := by grind

/-! # 4. Support and finite support -/

/-! ## Singletons and universes
A `pure` computation is supported on its value; a uniform draw is supported everywhere. -/

example (x : Bool) : support (pure x : ProbComp Bool) = {x} := by simp
example (x : Bool) : support (pure x : ProbComp Bool) = {x} := by grind

example : support ($ᵗ Bool) = Set.univ := by simp
example : support ($ᵗ Bool) = Set.univ := by grind

example : finSupport ($ᵗ (Fin 6)) = Finset.univ := by simp
example : finSupport ($ᵗ (Fin 6)) = Finset.univ := by grind

example : finSupport (pure true : ProbComp Bool) = {true} := by simp
example : finSupport (pure true : ProbComp Bool) = {true} := by grind

example : support ($ᵗ (Bool × Bool)) = Set.univ := by simp
example : support ($ᵗ (Bool × Bool)) = Set.univ := by grind

example : support ($ᵗ (Vector Bool 2)) = Set.univ := by simp
example : support ($ᵗ (Vector Bool 2)) = Set.univ := by grind

example : support (do let b ← $ᵗ Bool; pure b) = Set.univ := by simp
example : support (do let b ← $ᵗ Bool; pure b) = Set.univ := by grind

/-! ## Membership
Every value is a possible outcome of a uniform draw. -/

example (x : Bool) : x ∈ support ($ᵗ Bool) := by simp
example (x : Bool) : x ∈ support ($ᵗ Bool) := by grind

example (x : Bool) : x ∈ finSupport ($ᵗ Bool) := by simp
example (x : Bool) : x ∈ finSupport ($ᵗ Bool) := by grind

example (x : Bool) : x ∈ support (pure x : ProbComp Bool) := by simp
example (x : Bool) : x ∈ support (pure x : ProbComp Bool) := by grind

example (α : Type) [SampleableType α] (x : α) : x ∈ support ($ᵗ α) := by simp
example (α : Type) [SampleableType α] (x : α) : x ∈ support ($ᵗ α) := by grind

example (α : Type) [SampleableType α] : (support ($ᵗ α)).Nonempty := by simp
example (α : Type) [SampleableType α] : (support ($ᵗ α)).Nonempty := by grind

/-! ## The support ↔ probability bridge
A value has zero probability exactly when it is outside the support.

gap(simp): `simp` rewrites the `= 0` side to `x ∉ finSupport mx` and stops. Tagging
`mem_finSupport_iff_mem_support` `@[simp]` is not the fix: library proofs use `a ∈ finSupport oa`
as a *decidable* condition inside `dite` (`ProgramLogic/Relational/Quantitative.lean`), which the
`support` form loses. -/

example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] = 0 ↔ x ∉ support mx := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): stops at the `finSupport` form
  grind

example (mx : ProbComp Bool) (x : Bool) : 0 < Pr[= x | mx] ↔ x ∈ support mx := by simp
example (mx : ProbComp Bool) (x : Bool) : 0 < Pr[= x | mx] ↔ x ∈ support mx := by grind

/-! ## Event support via `Set.Nonempty`
An *event* has (non)zero probability exactly when some / no reachable output satisfies it. The
`grind`-friendly companions phrase this with `Set.Nonempty` of the filtered support
`{x ∈ support mx | p x}`, keeping the witness atomic where the `simp`-only `∃`/`∀ x ∈ support` forms
would saturate. -/

example (mx : ProbComp Bool) (p : Bool → Prop) :
    Pr[ p | mx] ≠ 0 ↔ {x ∈ support mx | p x}.Nonempty := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): `Set.Nonempty` companion, `grind`-shaped
  grind
example (mx : ProbComp Bool) (p : Bool → Prop) :
    Pr[ p | mx] = 0 ↔ ¬ {x ∈ support mx | p x}.Nonempty := by grind

/-! ## Structured supports
gap: a non-trivial `<$>`/`do` support equality needs `simp`'s computation normalisation and a set
extensionality; `grind` would expand it instead, and `simp` stops at the image of the set
literal. -/

example : support (do let b ← $ᵗ Bool; pure (!b)) = Set.univ := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): the image of a finite set literal
  fail_if_success grind  -- gap(grind, 2026-09-03): structured support
  ext b; cases b <;> simp

/-! # 5. Evaluation distribution — `𝒮[_]` -/

/-! ## `bind`/`pure` normalisation
A redundant `bind`/`pure` does not change the distribution. -/

example (mx : ProbComp Bool) : 𝒮[do let x ← mx; pure x] = 𝒮[mx] := by simp
example (mx : ProbComp Bool) : 𝒮[do let x ← mx; pure x] = 𝒮[mx] := by grind

example (mx : ProbComp Bool) : 𝒮[mx >>= pure] = 𝒮[mx] := by simp
example (mx : ProbComp Bool) : 𝒮[mx >>= pure] = 𝒮[mx] := by grind

/-! ## One-time-pad secrecy
Adding a uniform key makes the ciphertext distribution independent of the message (`ZMod 2` — a
one-bit XOR pad).

gap: this needs the translation-invariance lemma to fire before `evalSPMF_uniformSample` unfolds
the uniform draw, so it is `simp only`-terminal. -/

example (msg : ZMod 2) : 𝒮[(msg + ·) <$> ($ᵗ (ZMod 2))] = 𝒮[$ᵗ (ZMod 2)] := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): the uniform draw unfolds first
  fail_if_success grind  -- gap(grind, 2026-09-03): translation invariance is not a grind rule
  simp only [evalSPMF_add_left_uniform]

/-! # 6. The shape of `do`
The automation should see through the full surface syntax of `do`-notation: a pure `let :=`, nested
blocks, pattern-matching binds, `if`/`then`/`else`, and long chains. None of these can fail. -/

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

example : Pr[⊥ | coinThenNeg] = 0 := by grind [coinThenNeg]
example : Pr[⊥ | twoThenAnd] = 0 := by grind [twoThenAnd]
example : Pr[⊥ | nestedDraw] = 0 := by grind [nestedDraw]
example : Pr[⊥ | branchToFin] = 0 := by grind [branchToFin]
example : Pr[⊥ | fiveCoins] = 0 := by grind [fiveCoins]

example : Pr[= false | coinThenNeg] = Pr[= true | $ᵗ Bool] := by
  fail_if_success grind [coinThenNeg]  -- gap(grind, 2026-09-03): a `let :=` step under `do`
  simp [coinThenNeg]

/-- Abort unless the coin comes up `true`: fails with probability one half. -/
def abortOnFalse : OptionT ProbComp Bool := do
  let b ← $ᵗ Bool
  if b then pure true else failure

example : Pr[⊥ | abortOnFalse] = 2⁻¹ := by
  fail_if_success (simp [abortOnFalse]; done)  -- gap(simp, 2026-09-03): bind expansion, not simp
  simp [abortOnFalse, probFailure_bind_eq_add_tsum]

/-! # 7. Cryptography prerequisites
The kind of facts an intro-to-cryptography course assumes: guessing a uniform secret, collision
probability, and outcome probabilities summing to one. -/

example (guess : Fin 6) : Pr[= guess | $ᵗ (Fin 6)] = 6⁻¹ := by simp

example : Pr[fun p => p.1 = p.2 | $ᵗ (Fin 6 × Fin 6)] = 6 / 36 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-03): the filter card is not evaluated
  fail_if_success grind  -- gap(grind, 2026-09-03): counting
  simp; rfl

example : ∑ k : Fin 6, Pr[= k | $ᵗ (Fin 6)] = 1 := sum_probOutput_eq_one (by simp)

/-! # 8. Abstract carriers
The same facts over an arbitrary `SampleableType` carrier. `grind` handles the symbolic ones
(equiprobability, never-fails, nonempty support) and, through the `@[grind norm]` factorization
rule, the applicative product. -/

section abstract
variable (α β : Type) [SampleableType α] [SampleableType β]

example (x y : α) : Pr[= x | $ᵗ α] = Pr[= y | $ᵗ α] := by
  fail_if_success simp  -- gap(simp, 2026-09-03): no progress on abstract equiprobability
  grind

example : support ($ᵗ α) = Set.univ := by simp
example : support ($ᵗ α) = Set.univ := by grind

example (z : α × β) :
    Pr[= z | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] = Pr[= z.1 | $ᵗ α] * Pr[= z.2 | $ᵗ β] := by simp
example (z : α × β) :
    Pr[= z | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] = Pr[= z.1 | $ᵗ α] * Pr[= z.2 | $ᵗ β] := by grind

-- equiprobability of a uniform product: the `@[grind norm]` factorization rule lets bare `grind`
-- factor the applicative product, then close the equal factors
example (x y : α × β) :
    Pr[= x | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] = Pr[= y | (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] := by grind

end abstract

/-! # 9. Library-shape sentinels
Small facts in the shape of goals discharged throughout the library, to catch silent regressions of
the probability automation in isolation. -/

example (α : Type) [SampleableType α] (x : α) : x ∈ support ($ᵗ α) := by grind

example (mx : ProbComp Bool) (x : Bool) : Pr[= x | mx] = 0 ↔ x ∉ support mx := by grind

end VCVioTest.ProbabilityTactics
