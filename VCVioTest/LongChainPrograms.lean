/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Long-chain probability tactic benchmark

A third probability benchmark (companion to `VCVioTest/ProbabilityTactics.lean` and
`VCVioTest/MonadProbability.lean`) that exercises `simp` and `grind` over programs with **ten or
more sequential binds**, rather than the one/two-step shapes of the other two files. The point is to
pin down *where* on a long chain each tactic is strong: a regression in either surfaces here in
isolation.

The headline finding — the one this file gates — is that **`grind` keeps pace with `simp` on the
deep failure-probability telescope** (`Pr[⊥ | _] = 0` for a twelve-step `ProbComp`, where the chain
collapses through `probFailure_bind_eq_add_tsum` + each step never failing) and on **abstract
monad-law normalization** (redundant-`pure` chain over an opaque `m`, collapsed by the `@[grind =]`
laws `bind_pure`/`pure_bind`/`bind_assoc`/`map_pure`). These are genuinely long chains whose work is
all *structural*, away from the final arithmetic — exactly `grind`'s wheelhouse.

The complementary finding is that once a long chain bottoms out in a **concrete** distribution,
support set, or outcome-probability *value*, `grind` is the wrong tool: it dives into the
`PMF`/`SPMF` representation and either loses to `simp` or (for a numeric outcome) never closes it.
Those are recorded as `target(grind)` / `target(simp+grind)` notes, matching the convention of the
sibling files.

Conventions (as in the sibling files):
* **Mirrors.** Where both `simp` and `grind` close a goal, both are kept.
* **Single tactic + target.** Where only one closes it, that tactic is used and the gap is recorded
  with a `target(...)` note.
* **Only stable tactics.** No example hangs or explodes.
-/

open OracleComp ProbComp ENNReal

namespace VCVioTest.LongChainPrograms

/-! ## Programs

The named computations the benchmark reasons about. `chain12` / `chain12Opt` are twelve-step uniform
chains (over `ProbComp` and the failing carrier `OptionT ProbComp`); `coinPadded` a ten-deep tower
of redundant `pure` binds that is secretly just `$ᵗ Bool`; `longAbort` is a ten-step `OptionT` chain
with a single guard, so it fails with probability one half. -/

/-- A twelve-step chain of independent uniform draws. -/
def chain12 : ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool
  let i ← $ᵗ Bool; let j ← $ᵗ Bool; let k ← $ᵗ Bool; let l ← $ᵗ Bool
  pure (a && b && c && d && e && f && g && h && i && j && k && l)

/-- The same twelve-step chain over the failing carrier `OptionT ProbComp`; it still never fails. -/
def chain12Opt : OptionT ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool
  let i ← $ᵗ Bool; let j ← $ᵗ Bool; let k ← $ᵗ Bool; let l ← $ᵗ Bool
  pure (a && b && c && d && e && f && g && h && i && j && k && l)

/-- A ten-deep tower of redundant `pure` binds: `bind_pure`/`pure_bind` collapse it to `$ᵗ Bool`. -/
def coinPadded : ProbComp Bool := do
  let a ← $ᵗ Bool
  let b ← pure a; let c ← pure b; let d ← pure c; let e ← pure d
  let f ← pure e; let g ← pure f; let h ← pure g; let i ← pure h
  let j ← pure i; let k ← pure j
  pure k

/-- A ten-step `OptionT` chain with a single guard at the fifth step: fails with probability one
half, regardless of the nine surrounding uniform draws. -/
def longAbort : OptionT ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; guard e
  let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool; let i ← $ᵗ Bool; let j ← $ᵗ Bool
  pure (a && b && c && d && f && g && h && i && j)

/-! ## 1. The deep failure-probability telescope — `grind` keeps pace with `simp`

`Pr[⊥ | chain12] = 0` is a twelve-deep `probFailure_bind_eq_add_tsum` telescope bottoming out in
`Pr[⊥ | $ᵗ Bool] = 0` at each step. Both tactics drive it to `0`; this is the chain where `grind`
matches `simp`, and the main regression gate of the file. -/

example : Pr[⊥ | chain12] = 0 := by simp [chain12]
example : Pr[⊥ | chain12] = 0 := by grind [chain12]

/-! ## 2. The same chain over a failing carrier

Over `OptionT ProbComp` the telescope is `simp`'s: `grind` descends into the `OptionT`/`PMF`
plumbing instead of staying in the `probFailure` algebra.

Both the "never fails" and "can fail" *symbolic* facts close by `simp` at chain depth; the exact
failure *value* does not (the ten-deep `probFailure_bind_eq_add_tsum` telescope leaves a nested
`ℝ≥0∞` sum that `simp` does not normalise to a number — a `target(simp+grind)` like §5, `2⁻¹` for
`longAbort`).

target(grind): both close by `simp`, not `grind` (which descends into the `OptionT`/`PMF`
plumbing). -/

example : Pr[⊥ | chain12Opt] = 0 := by simp [chain12Opt]
example : Pr[⊥ | longAbort] ≠ 0 := by simp [longAbort, probFailure_bind_eq_add_tsum]

/-! ## 3. Structural normalization — abstract chain vs concrete head

A redundant-`pure` chain is pure monad-law rewriting. Over an **opaque** monad `m` (and over a free
`ProbComp` head that `grind` keeps atomic) `grind` collapses it just like `simp`. Once the head is
the **concrete** `$ᵗ Bool` of `coinPadded`, `grind` unfolds `𝒟` into `PMF.uniformOfFintype` and
loses the structural view, so the deep concrete normalization is `simp`'s. -/

section abstractHead
variable {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

example (mx : m α) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by simp
example (mx : m α) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by grind

-- target(grind): a deeper opaque-`m` tower normalises by `simp`; `grind`'s collapse is unstable.
example (mx : m α) :
    𝒟[do let a ← mx; let b ← pure a; let c ← pure b; pure c] = 𝒟[mx] := by simp

end abstractHead

example (mx : ProbComp Bool) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by simp
example (mx : ProbComp Bool) : 𝒟[do let a ← mx; pure a] = 𝒟[mx] := by grind

-- target(grind): with the concrete `$ᵗ Bool` head, the ten-deep `coinPadded` collapses by `simp`;
-- `grind` descends into the `PMF` representation and does not close these.
example : 𝒟[coinPadded] = 𝒟[($ᵗ Bool)] := by simp [coinPadded]
example : Pr[= true | coinPadded] = Pr[= true | $ᵗ Bool] := by simp [coinPadded]
example : support coinPadded = support ($ᵗ Bool) := by simp [coinPadded]

/-! ## 4. Support of a deep chain

A specific reachable point of `chain12`'s support is decided by `simp`.

target(grind): membership in / equality of a deep chain's support is `simp`'s; `grind` does not
close these. The full `support chain12 = Set.univ` is a `target(simp+grind)`: neither closes it in
one terminal step (it needs that the twelve-fold `&&` realises both booleans and the union
telescopes to the universe). -/

example : (false : Bool) ∈ support chain12 := by simp [chain12]

/-! ## 5. Outcome value of a multi-step chain — `target(simp+grind)`

Computing a concrete outcome probability of a multi-step bind chain is the one shape **neither**
terminal tactic closes: `simp` normalises the chain step by step but stops before collapsing the
nested `tsum` to a number, and `grind` does no `ℝ≥0∞` arithmetic. The canonical proof threads
`probOutput_bind_eq_tsum` and `tsum_eq_single` by hand. The benchmark records the gap rather than
carrying a multi-step proof; `chain12` returns `true` only when all twelve coins do, so

  `Pr[= true | chain12] = (2 ^ 12)⁻¹`   -- target(simp+grind)

is the representative outcome-value target. -/

end VCVioTest.LongChainPrograms
