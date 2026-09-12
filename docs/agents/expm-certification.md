# Certifying `expm_p63_error`

How the FACCT sampler kernel's error bound was proved, and the measurements behind each choice.
`expm_p63_error` lives in `Extern/Falcon/ExpmBridge.lean`; everything here is measured, not
estimated.

## The obligation

```
|expm_p63 x ccs / 2 ^ 63 - ccs * exp (-x)| ≤ 2 ^ (-51)
```
for `ccs ∈ [0, 1)` and `x ∈ [0, 0.694]`. Throughout, one **unit** means `2 ^ (-63)`, so the
budget is **4096 units**.

Two things about the domain are worth knowing.

`ccs < 1` is load-bearing on both sides. The routine reads its operands through a fixed-point
conversion that keeps `⌊2 ^ 63 · ccs⌋` in 63 bits and drops the sign bit. At `ccs = 1` the
conversion wraps to `0` and the whole product with it, for every `x` in range, against a true
value never below one half. Above `1` the claim fails outright: the returned `UInt64` read at
scale `2 ^ 63` is below `2`, while `ccs · exp (-x)` grows without bound.

`x ≤ 0.694` rather than `x < log 2` is deliberate. `0.694` is the smallest constant above `log 2`
the proof already carries — it is the contraction factor of the Horner error induction
(`scaledArg_le_694`), and the certificates run to `89/128 = 0.6953125`. Stating it there is what
lets a caller feed a *computed* reduction: a caller reducing modulo `log 2` by rounding a
floating-point quotient can land a few ulps above `log 2` when the argument is near a multiple of
it, and no statement closed at `log 2` would apply to it.

## Where the budget goes

| source | lemma | units |
| --- | --- | --- |
| fixed-point pipeline | `expm_p63_sub_trueArg_le` | 10 |
| 15 Chebyshev certificates | `abs_certQ_le` | 3574 |
| degree-18 Taylor truncation | `abs_taylorExpNeg_sub_exp_le` | 80 |
| **total** | `expm_p63_error` | **3664** of 4096 |

The bound is very nearly saturated, and by the approximation rather than the arithmetic around
it. A random sweep over the domain puts the true worst case near 3400 units, so the proved figure
carries about 10% of headroom over the measured one and 10% under the budget.

The fixed-point half is ordinary: `mulHi64` is the high half of the exact product, `mtwop63` is
*exactly* `⌊2 ^ 63 · toReal x⌋` with no rounding of its own, and the twelve Horner floors contract
because each step scales the previous error by `ζ < 0.694`. The loop's `UInt64` subtraction cannot
wrap for a cheap reason: `mulHi64 a b ≤ b` for **every** `a`.

## Why the obvious bounds do not work

Write `Q = P - T_n`, the difference between the coefficient polynomial and a Taylor truncation of
`exp (-x)`. `FPR.facctCoeffs` is a minimax fit, not a Taylor truncation — every coefficient is
perturbed from `2 ^ 63 / k!` (the linear one by `-47104`, the degree-12 one by `-1.3e8`). So `Q`
has `O(1)` coefficients while being `O(2 ^ -51)`: the fit earns its accuracy from cancellation
*across* the interval, and every bound that applies a triangle inequality to coefficients throws
that cancellation away.

| approach | result | vs 4096 |
| --- | --- | --- |
| Taylor, coefficient-wise + Lagrange remainder | `2 ^ (-35.8)` | ~38000x too weak |
| Chebyshev over the whole interval | 7529 units | 1.8x too weak |
| Midpoint + Lipschitz, 256 pieces | 2988783 units | 730x too weak |

The Lipschitz failure is the instructive one: bounding `sup |Q'|` coefficient-wise suffers the
*identical* pathology, so subdividing does not rescue it. What works is subdivision that restores
locality, applied to `Q` itself.

## Why Chebyshev, and why 15 pieces

| basis | pieces | bound | margin |
| --- | --- | --- | --- |
| Taylor form (shifted power basis) | 64 | 4083 | 0.3% — fails once truncation is added |
| Taylor form | 128 | 3589 | 12% |
| Taylor form | 256 | 3569 | 13% |
| **Chebyshev** | **32** | **3585** | **12%** |

Chebyshev at 32 pieces matches Taylor form at 128 — a 4x reduction in certificate count for the
price of needing `|T_j t| ≤ 1` on `[-1, 1]` (`abs_le_of_chebCert`). The landed proof gets to 15 by
making the covering non-uniform instead of uniform: `[0, 1/16]` in one piece, `[1/16, 1/8]` in
four of width `1/64`, `[1/8, 11/16]` in nine of width `1/16`, and `[11/16, 89/128]` in one of
width `1/128`. `abs_certQ_le` chains them and is where the covering is checked.

The Taylor degree is irrelevant to the bound: `n = 18`, `22` and `26` all give the same figure,
because the remainder is already negligible at 18 (0.07 units). The proof uses 18, via
`Real.exp_bound`.

## Cost, and clearing denominators

Each certificate is a polynomial identity of degree `n` under a linear substitution. Over `ℚ`
this is slow, and — counter-intuitively — reducing the degree does not help, because the cost
tracks the coefficient arithmetic rather than the degree:

| coefficients | degree | time (single certificate, incl. import) |
| --- | --- | --- |
| `ℚ`, 481 digits | 26 | 13.4 s |
| `ℚ`, 326 digits | 18 | 18.3 s |

**Clearing denominators fixes it.** The digit counts are denominator-dominated (`2 ^ 63`, `m ^ n`,
`n!`); one common scaling makes every coefficient an integer — this is why `certQ_expand` and the
`certN*` tables are stated over `ℤ`. Measured over `ℤ` at degree 18 with 326-digit coefficients,
several certificates to a file so the import is amortised: **2.54 s marginal per certificate** on
a 6.8 s import, against roughly 11.5 s marginal over `ℚ`. The whole certification layer costs
about 25 s of build time.

Breakpoints are **dyadic** for the same reason: anchoring the split at a decimal bound for `log 2`
produces 337-digit numerals, and the line-length linter cannot wrap a numeral.

## What was wrong before it was checked

Three figures in an earlier draft of this note were wrong, and each was corrected by measurement
rather than by argument:

- The fixed-point truncation was estimated at ~15 units. It is **1.55**, because `mtwop63`
  contributes nothing at all — it is exact.
- A `Float`-precision differential check reported the approximation's worst case as *exactly* the
  4096-unit budget. Near `2 ^ 63` its own rounding is ~2000 units of `2 ^ (-63)`. Redone in exact
  arithmetic the true worst case is around 3560.
- Build time was expected to be the binding constraint on the basis choice. After clearing
  denominators it is not.

Check tight numeric constants in exact arithmetic, not floats.
