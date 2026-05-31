# Notation Reference

## OracleSpec Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `A →ₒ B` | Singleton oracle spec (`OracleSpec.ofFn`) | `VCVio/OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec (`emptySpec`) | `VCVio/OracleComp/OracleSpec.lean` |
| `spec₁ + spec₂` | Combine specs via `Sum.elim` | `VCVio/OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation | `VCVio/OracleComp/Coercions/SubSpec.lean` |
| `∘ₛ` | QueryImpl composition | `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions.lean` |

## Probability Notations

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `𝒟[mx]` | `evalDist mx` | `VCVio/EvalDist/Defs/Basic.lean` |
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

## Lattice Norms

Scoped notation (`open scoped LatticeCrypto`, or inside `namespace LatticeCrypto`)
for the centered polynomial norms in `LatticeCrypto/Ring/Norms.lean`. The trailing
subscript on the closing bar keeps these distinct from Mathlib's `‖·‖`
(`Norm.norm`); none of these are Mathlib `Norm` instances (they live in `ℕ`).

### Bare bars — canonical `ZMod q` vector backend (`Poly (ZMod q) n`)

| Notation | Meaning | Input method |
|----------|---------|--------------|
| `‖p‖∞` | `cInfNorm p` (centered `ℓ∞`) | `\|\|` … `\infty` |
| `‖p‖₁` | `l1Norm p` (`ℓ₁`) | `\|\|` … `\1` |
| `‖p‖₂²` | `l2NormSq p` (squared `ℓ₂`) | `\|\|` … `\2\^2` |
| `‖(p₁, p₂)‖₂²` | `pairL2NormSq p₁ p₂` | as above |

### `⟪ops⟫`-annotated bars — a `NormOps` bundle `ops`

Overloaded for a single backend polynomial (`NormOps.*`) and, by the same syntax,
for a `PolyVec` (`PolyVec.*`); elaboration picks the type-correct one. `⟪ ⟫` is
`\langle\langle` / `\rangle\rangle`.

| Notation | Meaning |
|----------|---------|
| `‖f‖⟪ops⟫∞` | `ops.cInfNorm f` / `PolyVec.cInfNorm ops f` |
| `‖f‖⟪ops⟫₁` | `ops.l1Norm f` |
| `‖f‖⟪ops⟫₂²` | `ops.l2NormSq f` / `PolyVec.l2NormSq ops f` |
| `‖(s₁, s₂)‖⟪ops⟫₂²` | `ops.pairL2NormSq s₁ s₂` |

Scheme-local norm aliases (`Falcon.pairL2NormSq`, `MLDSA.polyNorm`, …) are *not*
these globals and keep their named form.

## Legacy Notation (Do NOT Use)

| Dead notation | Replacement |
|---------------|-------------|
| `[= x \| comp]` | `Pr[= x \| comp]` |
| `++ₒ` | `+` |
