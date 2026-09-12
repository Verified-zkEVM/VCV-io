# Notation Reference

## OracleSpec Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `A →ₒ B` | Singleton oracle spec (`OracleSpec.ofFn`) | `VCVio/OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec (`emptySpec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `spec₁ + spec₂` | PFunctor coproduct (dependent `Sum.rec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation | `VCVio/OracleComp/Coercions/SubSpec.lean` |
| `∘ₛ` | QueryImpl composition | `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions.lean` |

## Probability Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝒟[mx]` | primary `Measure` denotation, `evalDist mx` | `VCVio/EvalDist/Defs/Measure.lean` |
| `𝒮[mx]` | explicit finite adapter, `evalSPMF mx` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[= x \| mx]` | `probOutput mx x` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[p \| mx]` | `probEvent mx p` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[⊥ \| mx]` | `probFailure mx` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[cond \| var ← src]` | `probEvent src (fun var => cond)` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr_{let x ← mx}[p x]` | event probability using an ordinary Lean sampling block | `VCVio/EvalDist/Notation.lean` |

Import `VCVio.EvalDist.Notation` and use `open scoped ProbabilityTheory` for
`Pr_{...}[...]`. The braces accept Lean's standard `doSeq` grammar, including multiple dependent
samples, pattern bindings, local declarations, and mutable variables. The event is appended as the
final return of the same `do` block; it can use all bindings still in scope. Early returns have their
ordinary Lean meaning and return a proposition directly, skipping the appended event. The notation
is an alias of `Pr{...}[...]`; it preserves failure mass and does not select an interpretation or
initial state. `probOutput_true_eq_probEvent` connects a single-sample block to `Pr[p | mx]`.

**NOTE**: Legacy code and comments may still use the old `[= x | comp]` notation (without `Pr` prefix). Always use `Pr[...]` in new code.

`Pr[...]` is a discrete compatibility notation. Use `probOutput_eq_evalDist`,
`probEvent_eq_evalDist`, or `probFailure_eq_evalDist` to move a scalar statement to `𝒟[...]`.

### Coordinated ArkLib adoption

ArkLib's `ArkLib/Data/Probability/Notation.lean` defines the same `Pr_{...}[...]` spelling in
the `ProbabilityTheory` scope. Its local parser and macro must be removed when its VCVio dependency
is updated to include this module: enabling both definitions produces ambiguous terms.
Keep ArkLib's existing import path as a compatibility module importing `VCVio.EvalDist.Notation`
and `VCVio.EvalDist.Defs.Instances`. Retain `$ᵖ` and the mathematical helper lemmas in ArkLib.
Existing call sites and `open scoped ProbabilityTheory` declarations can keep their spelling.

The probability is unchanged, but the expansion is no longer definitionally a raw distribution
application. At a proof boundary, `PMF.probOutput_eq_apply` identifies the new observation with
`(do ...; return event) True`. Use that public equation where an old `rfl` or restricted unfolding
proof depended on the expansion; generic event proofs can use `probOutput_true_eq_probEvent`.
Validate the combined dependency/import change and the ArkLib probability and coding-theory
callers before coordinating the merge. The notation PR remains draft pending that validation.

## Sampling Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `$ᵗ T` | `uniformSample T` (type-level uniform) | `VCVio/OracleComp/Constructions/SampleableType.lean` |
| `$ xs` | `uniformSelect xs` (can fail on empty) | `VCVio/OracleComp/ProbComp.lean` |
| `$! xs` | `uniformSelect! xs` (never fails) | `VCVio/OracleComp/ProbComp.lean` |
| `$[0..n]` | `uniformFin n` (uniform `Fin (n+1)`) | `VCVio/OracleComp/ProbComp.lean` |
| `$[n⋯m]` | `uniformRange n m` (uniform over range) | `VCVio/OracleComp/ProbComp.lean` |

## Program Logic Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝟙⟦P⟧` | Numeric proposition indicator (`propInd P`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `⌜P⌝` | Loom pure proposition assertion | `VCVio/ProgramLogic/NotationCore.lean` |
| `wp⟦c⟧` | Quantitative WP (`wp c`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `rwp⟦c₁ ~ c₂ \| post; epost₁, epost₂⟧` | Relational WP (`Std.Do'.rwp c₁ c₂ post epost₁ epost₂`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `⦃P⦄ c ⦃Q⦄` | Loom unary Hoare triple (`Std.Do'.Triple`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `g₁ ≡ₚ g₂` | Game equivalence (`GameEquiv`) | `VCVio/ProgramLogic/NotationCore.lean` |
| `⟪c₁ ~ c₂ \| R⟫` | pRHL coupling (`RelTriple c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⟪c₁ ≈[ε] c₂ \| R⟫` | Approximate coupling (`ApproxRelTriple ε c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | Quantitative relational triple (`Std.Do'.RelTriple f c₁ c₂ g Lean.Order.bot Lean.Order.bot`) | `VCVio/ProgramLogic/Notation.lean` |

## UC Composition Notations

Scoped to `Interaction.UC` (activated by `open Interaction.UC`).
Defined in `PolyFun/Interaction/UC/Notation.lean`.

### Boundary-level

| Notation | Meaning | Input method |
|----------|---------|--------------|
| `Δ₁ ⊗ᵇ Δ₂` | `PortBoundary.tensor Δ₁ Δ₂` | `\otimes ^b` |
| `Δᵛ` | `PortBoundary.swap Δ` (dual/flip) | `\^v` |

### Expression-level (typeclass-backed)

Works for `Raw`, `Expr`, and `Interp` via `HasPar`/`HasWire`/`HasPlug` typeclasses.
Each type has `@[simp]` bridge lemmas (e.g., `Raw.hasPar`) that normalize
`HasPar.par e₁ e₂` back to `Raw.par e₁ e₂`, so existing simp lemmas
(`interpret_par`, etc.) fire transparently.

| Notation | Meaning | Prec | Input method |
|----------|---------|------|--------------|
| `e₁ ∥ e₂` | `HasPar.par e₁ e₂` (parallel) | 70r | `\parallel` |
| `e₁ ⊞ e₂` | `HasWire.wire e₁ e₂` (wire) | 65r | `\boxplus` |
| `e ⊠ k` | `HasPlug.plug e k` (plug/close) | 60r | `\boxtimes` |

Precedence ensures `A ∥ B ⊞ C ⊠ K` parses as `((A ∥ B) ⊞ C) ⊠ K`.

## Legacy Notation (Do NOT Use)

| Dead notation | Replacement |
|---------------|-------------|
| `[= x \| comp]` | `Pr[= x \| comp]` |
| `++ₒ` | `+` |
