/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import Interop.Hax.Bridge
import Interop.Rust.Run
import Hax.rust_primitives.Cast
import Hax.rust_primitives.BVDecide
import Hax.Tactic
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Instances.ErrorT
import VCVio.EvalDist.Instances.OptionT
import VCVio.EvalDist.Fintype

/-!
# End-to-end hax example: centered-binomial sampler (CBD, η = 1)

The first `Interop.Hax` example whose probabilistic content is
**intrinsic to the Rust code**, not bolted on from the VCVio side.

## Provenance

The Rust source lives at `third_party/hax-cbd/src/lib.rs`:

```rust
pub fn sample_cbd1(b: u8) -> i32 {
    let a = (b & 1) as i32;
    let c = ((b >> 1) & 1) as i32;
    a - c
}
```

Running `cargo hax into lean` produces
`third_party/hax-cbd/proofs/lean/extraction/hax_cbd.lean`; the `def
sample_cbd1` below is the verbatim hax emission (modulo the `Interop`
namespace).

## What this demonstrates

`sample_cbd1` is one step of ML-KEM's `SamplePolyCBD_η` noise sampler
at parameter `η = 1`: given one byte of uniform randomness it returns
a single signed field-element in `{-1, 0, 1}`, distributed as the
centered binomial with parameter 1 (i.e. `Bernoulli(1/2) -
Bernoulli(1/2)`). Only the low two bits of `b` affect the output.

Unlike `Barrett.lean`, `Computation.lean`, and `Adc.lean`, whose
inputs are data and whose outputs are deterministic, `sample_cbd1`'s
input **is** randomness. The bridge then lets us make two
complementary statements on the two sides:

* On the hax / `RustM` side, `sample_cbd1_run_in_range` establishes
  the bound `r ∈ {-1, 0, 1}` for every `u8` input. We prove it at the
  `.run` level via `decide` over the 256 possible `u8` values, rather
  than through `hax_bv_decide` on a `Triple`: the `u8 → i32` widening
  in the body goes through `UInt8.toInt32`, which the bit-blast
  backend abstracts as opaque. Every other example in this folder
  covers the `Triple` / bit-blast pattern; CBD covers the
  complementary `.run` / `decide` pattern, which is what's available
  whenever a `u8 → i*` widening appears in the body.
* On the VCVio / `RustOracleComp` side, `sampleRandomCbd1_prob_zero`
  (and its `+1` / `-1` siblings) establish the **exact distribution**
  `Pr[0] = 1/2`, `Pr[±1] = 1/4`. This is the claim that only makes
  sense on this side of the bridge: the `Triple` layer is universal
  over oracle outcomes, and `Hax.RustM` has no oracle at all.

`sampleRandomCbd1` samples from `Fin 4` (the two relevant bits)
rather than from a full `u8`. The output distribution is the same as
sampling a full byte and passing it to `sample_cbd1` (the six high
bits are unused), but restricting the input space to four values
keeps the peel + enumeration proof short. Extending to the full
8-bit version is a pushforward argument and is left as a follow-up.

## Scaling path

ML-KEM-512 uses the same pattern at `η = 2` (4 bits in, one coefficient
out, so a byte yields two coefficients). ML-KEM-768/1024 uses `η = 2`
for both secret and noise, and ML-KEM-512 uses `η = 3` for the secret.
Each of those samplers is a one-page hax function of the same shape,
verifiable by the same `decide` on the hax side and the same
enumeration on the VCVio side. Wrapping into a 256-coefficient loop
is the next step up.
-/

open Std.Do OracleSpec OracleComp ENNReal

namespace Interop.Hax.Examples.CenteredBinomial

variable {ι : Type} {spec : OracleSpec ι}

/-! ### Hax emission

Verbatim hax output, namespaced into `Interop.Hax.Examples.CenteredBinomial`. The
regenerate-from-source pipeline is: edit `third_party/hax-cbd/src/lib.rs`,
run `cargo hax into lean`, copy the emitted definition here. Three
checked operations (bitwise AND on `u8`, right shift by `1`, widening
cast `u8 → i32`) and one subtraction on `i32`; none of them can fail
on a `u8` input, so the `RustM` monad is carried for shape alone. -/

/-- Centered binomial distribution (η = 1) sampler, emitted by hax.
Takes one byte, returns `a - c` where `a = b & 1` and `c = (b >> 1) & 1`
are the low two bits of `b` widened to `i32`. Only bits 0 and 1 of `b`
are read. -/
@[spec]
def sample_cbd1 (b : u8) : RustM i32 := do
  let a : i32 ← (rust_primitives.hax.cast_op (← (b &&&? (1 : u8))) : RustM i32)
  let c : i32 ←
    (rust_primitives.hax.cast_op
      (← ((← (b >>>? (1 : i32))) &&&? (1 : u8))) :
      RustM i32)
  (a -? c)

/-! ### Constructor-level evaluation on the four bit-patterns

Each of the four `b &&& 3` patterns reduces `sample_cbd1 b` to a
`RustM.ok` constructor with a concrete `i32` value. These are the
only `sample_cbd1` evaluations `sampleRandomCbd1` ever encounters.
The concrete `u8` inputs let the bitwise ops, shift, cast, and
subtraction all reduce definitionally. -/

@[simp] theorem sample_cbd1_val_0 :
    sample_cbd1 (0 : u8) = (RustM.ok (0 : i32)) := rfl

@[simp] theorem sample_cbd1_val_1 :
    sample_cbd1 (1 : u8) = (RustM.ok (1 : i32)) := rfl

@[simp] theorem sample_cbd1_val_2 :
    sample_cbd1 (2 : u8) = (RustM.ok (-1 : i32)) := rfl

@[simp] theorem sample_cbd1_val_3 :
    sample_cbd1 (3 : u8) = (RustM.ok (0 : i32)) := rfl

set_option linter.style.nativeDecide false in
/-- Total-correctness statement: every `u8` input yields an `ok`
output in `{-1, 0, 1}`. Proved by `native_decide` exhausting the 256
`u8` values (pure `decide` exceeds Lean's default recursion depth on
this size of a search space). -/
theorem sample_cbd1_run_in_range (b : u8) :
    (sample_cbd1 b).run = some (Except.ok (-1 : i32)) ∨
    (sample_cbd1 b).run = some (Except.ok 0) ∨
    (sample_cbd1 b).run = some (Except.ok 1) := by
  revert b
  native_decide

/-! ### Oracle-lifted sampler

The lift is one line, as in `Barrett.lean` / `Computation.lean` etc.
No `Triple`-level transport lemma here because the source statement
lives at the `.run` level rather than as a `Triple`. -/

/-- Lift of `sample_cbd1` into `RustOracleComp spec`. Neither side of
the bridge issues any oracle query. -/
def sample_cbd1_Lifted (b : u8) : Interop.Rust.RustOracleComp spec i32 :=
  liftRustM (sample_cbd1 b)

/-! ### Randomized sampler

Draw two uniform bits (encoded as `Fin 4`), cast into a `u8`, and
apply the hax-emitted `sample_cbd1`. This is the first `Interop.Hax`
program in which the randomness feeds into the Rust code proper,
rather than only into an external branch selector. -/

/-- Randomized CBD(η = 1) sampler. Draws a uniform two-bit value `n`
and runs `sample_cbd1 (UInt8.ofNat n.val)`. Equivalent in distribution
to sampling a full byte (the six high bits are unused). -/
def sampleRandomCbd1 : Interop.Rust.RustOracleComp unifSpec i32 := do
  let n ← ($[0..3] : ProbComp (Fin 4))
  sample_cbd1_Lifted (UInt8.ofNat n.val)

/-- Peel of `sampleRandomCbd1` to `OracleComp unifSpec`. The four
outcomes of the `Fin 4` draw determine the output deterministically
via the four `sample_cbd1_val_{0,1,2,3}` constructor equations. -/
theorem sampleRandomCbd1_run_run :
    sampleRandomCbd1.run.run =
      ($[0..3] >>= fun n : Fin 4 =>
        pure (some (if n = 0 ∨ n = 3 then
          (Except.ok (0 : i32) : Except Interop.Rust.Error i32)
         else if n = 1 then
          Except.ok (1 : i32)
         else
          Except.ok (-1 : i32))) :
            OracleComp unifSpec (Option (Except Interop.Rust.Error i32))) := by
  unfold sampleRandomCbd1 sample_cbd1_Lifted
  simp only [Interop.Rust.RustOracleComp.run_run_bind_liftM]
  refine bind_congr fun n => ?_
  fin_cases n <;> simp [UInt8.ofNat, Interop.Hax.liftRustM_ok]

/-! ### Distribution

Three exact probability statements, together characterizing the
CBD(η = 1) distribution on the output of `sampleRandomCbd1`. Each is
a `simp` / `norm_num` calculation on the four-term sum produced by
the peel. -/

/-- ENNReal arithmetic used by `sampleRandomCbd1_prob_zero` below:
`1/4 + 1/4 = 1/2`. Factored out because `norm_num` does not close it
directly over `ℝ≥0∞`. -/
private lemma ennreal_inv_four_add_inv_four :
    (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  rw [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-- Numeric rewrite shared by the three probability lemmas below:
`ProbComp.probOutput_uniformFin` hands back `((3 : ℕ) + 1 : ℝ≥0∞)⁻¹`
rather than `4⁻¹`, so collapse the cast + sum before pattern-matching
on `4⁻¹`. -/
private lemma three_add_one_ennreal : ((3 : ℕ) + 1 : ℝ≥0∞) = 4 := by norm_num

private abbrev cbdOutputZero : Option (Except Interop.Rust.Error i32) :=
  some (Except.ok (0 : i32))

private abbrev cbdOutputPosOne : Option (Except Interop.Rust.Error i32) :=
  some (Except.ok (1 : i32))

private abbrev cbdOutputNegOne : Option (Except Interop.Rust.Error i32) :=
  some (Except.ok (-1 : i32))

private lemma probOutput_pure_cbd_zero_zero :
    Pr[= cbdOutputZero | (pure cbdOutputZero : OracleComp unifSpec _)] = 1 :=
  probOutput_pure_self cbdOutputZero

private lemma probOutput_pure_cbd_zero_pos :
    Pr[= cbdOutputZero | (pure cbdOutputPosOne : OracleComp unifSpec _)] = 0 := by
  rw [probOutput_pure]
  have h : cbdOutputZero ≠ cbdOutputPosOne := by decide
  simp [h]

private lemma probOutput_pure_cbd_zero_neg :
    Pr[= cbdOutputZero | (pure cbdOutputNegOne : OracleComp unifSpec _)] = 0 := by
  rw [probOutput_pure]
  have h : cbdOutputZero ≠ cbdOutputNegOne := by decide
  simp [h]

private lemma probOutput_pure_cbd_pos_zero :
    Pr[= cbdOutputPosOne | (pure cbdOutputZero : OracleComp unifSpec _)] = 0 := by
  rw [probOutput_pure]
  have h : cbdOutputPosOne ≠ cbdOutputZero := by decide
  simp [h]

private lemma probOutput_pure_cbd_pos_pos :
    Pr[= cbdOutputPosOne | (pure cbdOutputPosOne : OracleComp unifSpec _)] = 1 :=
  probOutput_pure_self cbdOutputPosOne

private lemma probOutput_pure_cbd_pos_neg :
    Pr[= cbdOutputPosOne | (pure cbdOutputNegOne : OracleComp unifSpec _)] = 0 := by
  rw [probOutput_pure]
  have h : cbdOutputPosOne ≠ cbdOutputNegOne := by decide
  simp [h]

private lemma probOutput_pure_cbd_neg_zero :
    Pr[= cbdOutputNegOne | (pure cbdOutputZero : OracleComp unifSpec _)] = 0 := by
  rw [probOutput_pure]
  have h : cbdOutputNegOne ≠ cbdOutputZero := by decide
  simp [h]

private lemma probOutput_pure_cbd_neg_pos :
    Pr[= cbdOutputNegOne | (pure cbdOutputPosOne : OracleComp unifSpec _)] = 0 := by
  rw [probOutput_pure]
  have h : cbdOutputNegOne ≠ cbdOutputPosOne := by decide
  simp [h]

private lemma probOutput_pure_cbd_neg_neg :
    Pr[= cbdOutputNegOne | (pure cbdOutputNegOne : OracleComp unifSpec _)] = 1 :=
  probOutput_pure_self cbdOutputNegOne

/-- `Pr[output = 0] = 1/2` under `sampleRandomCbd1`. The two
bit-patterns `00` (`n = 0`) and `11` (`n = 3`) both map to `0`, so
exactly half the four equiprobable inputs yield the zero output.

The proof peels the `$[0..3]` draw, evaluates each of the four `pure`
branches against the zero target, and closes the resulting `4⁻¹ + 4⁻¹
= 2⁻¹` via `ennreal_inv_four_add_inv_four`. The concrete
`probOutput_pure_cbd_*` lemmas keep this proof from repeatedly
synthesizing large decidable equality instances for `i32` outputs. -/
theorem sampleRandomCbd1_prob_zero :
    Pr[= some (Except.ok (0 : i32)) | sampleRandomCbd1.run.run] = 2⁻¹ := by
  rw [sampleRandomCbd1_run_run, HasEvalSPMF.probOutput_bind_eq_sum_fintype,
    Fin.sum_univ_four]
  change _ * Pr[= cbdOutputZero | (pure cbdOutputZero : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputZero | (pure cbdOutputPosOne : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputZero | (pure cbdOutputNegOne : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputZero | (pure cbdOutputZero : OracleComp unifSpec _)] = _
  simp only [ProbComp.probOutput_uniformFin, three_add_one_ennreal,
    probOutput_pure_cbd_zero_zero, probOutput_pure_cbd_zero_pos,
    probOutput_pure_cbd_zero_neg, mul_one, mul_zero, add_zero]
  exact ennreal_inv_four_add_inv_four

/-- `Pr[output = +1] = 1/4` under `sampleRandomCbd1`. Only `n = 1`
contributes (bit pattern `01`, `a = 1`, `c = 0`), one of four
equiprobable draws. -/
theorem sampleRandomCbd1_prob_pos_one :
    Pr[= some (Except.ok (1 : i32)) | sampleRandomCbd1.run.run] = 4⁻¹ := by
  rw [sampleRandomCbd1_run_run, HasEvalSPMF.probOutput_bind_eq_sum_fintype,
    Fin.sum_univ_four]
  change _ * Pr[= cbdOutputPosOne | (pure cbdOutputZero : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputPosOne | (pure cbdOutputPosOne : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputPosOne | (pure cbdOutputNegOne : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputPosOne | (pure cbdOutputZero : OracleComp unifSpec _)] = _
  simp only [ProbComp.probOutput_uniformFin, three_add_one_ennreal,
    probOutput_pure_cbd_pos_zero, probOutput_pure_cbd_pos_pos,
    probOutput_pure_cbd_pos_neg, mul_one, mul_zero, add_zero, zero_add]

/-- `Pr[output = -1] = 1/4` under `sampleRandomCbd1`. Only `n = 2`
contributes (bit pattern `10`, `a = 0`, `c = 1`), one of four
equiprobable draws. -/
theorem sampleRandomCbd1_prob_neg_one :
    Pr[= some (Except.ok (-1 : i32)) | sampleRandomCbd1.run.run] = 4⁻¹ := by
  rw [sampleRandomCbd1_run_run, HasEvalSPMF.probOutput_bind_eq_sum_fintype,
    Fin.sum_univ_four]
  change _ * Pr[= cbdOutputNegOne | (pure cbdOutputZero : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputNegOne | (pure cbdOutputPosOne : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputNegOne | (pure cbdOutputNegOne : OracleComp unifSpec _)] +
      _ * Pr[= cbdOutputNegOne | (pure cbdOutputZero : OracleComp unifSpec _)] = _
  simp only [ProbComp.probOutput_uniformFin, three_add_one_ennreal,
    probOutput_pure_cbd_neg_zero, probOutput_pure_cbd_neg_pos,
    probOutput_pure_cbd_neg_neg, mul_one, mul_zero, add_zero, zero_add]

end Interop.Hax.Examples.CenteredBinomial
