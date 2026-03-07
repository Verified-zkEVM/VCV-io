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
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | eRHL triple (`eRelTriple f c₁ c₂ g`) | `VCVio/ProgramLogic/Notation.lean` |

## Legacy Notation (Do NOT Use)

| Dead notation | Replacement |
|---------------|-------------|
| `[= x \| comp]` | `Pr[= x \| comp]` |
| `++ₒ` | `+` |
