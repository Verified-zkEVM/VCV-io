# Notation Reference

## OracleSpec Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `A →ₒ B` | Singleton oracle spec (`OracleSpec.ofFn`) | `VCVio/OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec (`emptySpec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `spec₁ + spec₂` | Combine specs via `Sum.elim` | `VCVio/OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation | `VCVio/OracleComp/Coercions/SubSpec.lean` |
| `∘ₛ` | QueryImpl composition | `VCVio/OracleComp/SimSemantics/Constructions.lean` |

## Probability Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `Pr[= x \| mx]` | `probOutput mx x` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[p \| mx]` | `probEvent mx p` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[⊥ \| mx]` | `probFailure mx` | `VCVio/EvalDist/Defs/Basic.lean` |
| `Pr[cond \| var ← src]` | `probEvent src (fun var => cond)` | `VCVio/EvalDist/Defs/Basic.lean` |

**NOTE**: Legacy code and comments may still use the old `[= x | comp]` notation (without `Pr` prefix). Always use `Pr[...]` in new code.

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
| `⌜P⌝` | Prop indicator (`propInd P`) | `VCVio/ProgramLogic/Notation.lean` |
| `wp⟦c⟧` | Quantitative WP (`wp c`) | `VCVio/ProgramLogic/Notation.lean` |
| `⦃P⦄ c ⦃Q⦄` | Hoare triple (`Triple P c Q`) | `VCVio/ProgramLogic/Notation.lean` |
| `g₁ ≡ₚ g₂` | Game equivalence (`GameEquiv`) | `VCVio/ProgramLogic/Notation.lean` |
| `⟪c₁ ~ c₂ \| R⟫` | pRHL coupling (`RelTriple c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⟪c₁ ≈[ε] c₂ \| R⟫` | Approximate coupling (`ApproxRelTriple ε c₁ c₂ R`) | `VCVio/ProgramLogic/Notation.lean` |
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | Quantitative relational triple (`Std.Do'.RelTriple f c₁ c₂ g Lean.Order.bot Lean.Order.bot`) | `VCVio/ProgramLogic/Notation.lean` |

## UC Composition Notations

Scoped to `Interaction.UC` (activated by `open Interaction.UC`).
Defined in `VCVio/Interaction/UC/Notation.lean`.

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
