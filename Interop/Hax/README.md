# Interop / Hax

Bridge from [hax](<anonymized-repo-url>)'s Lean backend (`Hax.RustM`)
to VCVio's `RustOracleComp`.

## Status

`require Hax` is **active** in `lakefile.lean`, pinned to commit
`492a34e3` (hax `main` as of 2026-04-16). Hax compiles cleanly against our
Lean v4.29.0 / Mathlib v4.29.0 stack: `lake build Hax` succeeds in 91 jobs
with 2 harmless `@[reducible]` warnings in hax's own
`rust_primitives/USize64.lean`.

Bridge code is in place:

- `Bridge.lean` — `errorOfHax`, `liftRustM`, the `MonadLift RustM
  (Interop.Rust.RustOracleComp spec)` instance, five `rfl`-level
  `@[simp]` commutation lemmas (`liftRustM_{ok,fail,div,pure,bind}`),
  a `LawfulMonadLift` instance and a bundled `MonadHom`
  (`liftRustMHom`) that witnesses `liftRustM` as a monad morphism, and
  the compositional `Triple`-level boundary lemma `triple_liftRustM`,
  which is now registered as `@[spec]` so `mvcgen` auto-peels it.
- `Examples.lean` — hand-crafted end-to-end demo: a checked-addition
  `RustM` function, two equality-level specs, a `Std.Do.Triple` spec
  closed in a single `mvcgen` call thanks to `@[spec] triple_liftRustM`
  (`addOrPanicLifted_triple`), an oracle-composed `RustOracleComp`
  program (`oracleThenAdd`), a `Triple` spec on the oracle-composed
  program (`oracleThenAdd_triple`) that mixes a real `query` with a
  lifted `RustM` call, and a probabilistic `tossedAdd` harness whose
  panic probability (`1/2`) is proven via the reusable `.run.run`
  peel lemmas in `Interop/Rust/Run.lean`.
- `Computation.lean` — first example where the `RustM` side is real
  hax output, not a hand-crafted `RustM` definition. Lifts and proves
  a spec for `const fn computation(x: u32) -> u32 { x + x + 1 }` (from
  hax's `tests/lean-tests/src/constants.rs`), using hax's own
  `UInt32.haxAdd_spec` and the `triple_liftRustM` boundary lemma.
- `Division.lean` — second real-hax-output example, exercising the
  `.divisionByZero` branch of `errorOfHax` both at the Triple level
  (precondition-gated, via `UInt32.haxDiv_spec`) and at the equality
  level (`checkedDivLifted_fail_of_zero`), plus a probabilistic
  `randomDiv` whose panic probability (`1/2`, on `.divisionByZero`
  rather than `.integerOverflow`) is proven with the same peel lemmas.
- `Adc.lean` — flagship stress test: the `lean_adc` example from hax's
  own test suite (32-bit ADC with a `u64` intermediate), proved with
  `hax_mvcgen [adc_u32] <;> bv_decide` on the `RustM` side and lifted
  by `triple_liftRustM` to `RustOracleComp`. This is the high-
  automation end of the bridge: no user arithmetic, no transformer
  plumbing; once the Rust-side proof closes, the lifted proof is one
  line.
- `Barrett.lean` — first genuinely lattice-cryptographic hax example:
  the signed Barrett reduction `barrett_reduce` from hax's
  `examples/lean_barrett` (the ML-KEM / Kyber modular reduction by
  `q = 3329`). Proved with `hax_bv_decide (timeout := 90)` on the
  `RustM` side over five chained checked operations (`*?` / `+?` /
  `-?` / `>>>?`) and two cross-width casts (`i32 ↔ i64`); lifted to
  `RustOracleComp` in one line. Also bundles `oracleThenBarrett`, an
  oracle-composed version that samples a field coefficient, reduces
  it, and proves (via `wpProp_iff_forall_support` plus
  `Triple.entails_wp_of_post` on `barrett_reduce_Lifted_spec`) that
  the result always lands in the representative window
  `(-FIELD_MODULUS, FIELD_MODULUS)`.

`lake build Interop` succeeds across all of the above.

### `require` order

`require Hax` must appear *before* `require "leanprover-community" /
"mathlib"` in `lakefile.lean`. Mathlib's transitive pin of `Qq` has to win
over hax's `v4.29.0-rc1` pin, and Lake's conflict resolution takes the
**last** `require` of each dependency. `lake update` warns explicitly if
the order is wrong (`mathlib: failed to fetch cache`).

## What the bridge provides

On the monad side:

```
Hax.RustM α  :=  ExceptT _root_.Error Option α
     |
     | liftRustM (MonadLift)
     v
Interop.Rust.RustOracleComp spec α
             :=  ExceptT Interop.Rust.Error (OptionT (OracleComp spec)) α
```

`liftRustM` pattern-matches on the three cases of `RustM` and maps them to
the corresponding `RustOracleComp` constructors, rebranding the `Error`
enum constructor-by-constructor via `errorOfHax`. No oracle query is
issued by the lift.

On the Hoare-logic side, `Std.Do`'s `ExceptT.instWP` and `OptionT.instWP`
compose VCVio's `WP (OracleComp spec) .pure` (from
`VCVio.ProgramLogic.Unary.StdDoBridge`) into the same WP shape hax uses
for `RustM` itself, namely `.except Error (.except PUnit .pure)`, modulo
the `Error` rebrand. Because the shape matches, `mvcgen` walks lifted
Rust programs with no bespoke transformer lemmas; the `@[simp]`
commutation rules peel `liftRustM` off concrete constructors.

## Minimal example (see `Examples.lean`)

```lean
def addOrPanic (x y : Nat) : RustM Nat :=
  if x + y < 2 ^ 32 then pure (x + y) else RustM.fail .integerOverflow

def addOrPanicLifted (x y : Nat) : Interop.Rust.RustOracleComp spec Nat :=
  liftRustM (addOrPanic x y)

theorem addOrPanicLifted_triple (x y : Nat)
    [spec.Fintype] [spec.Inhabited] :
    ⦃⌜x + y < 2 ^ 32⌝⦄
    (addOrPanicLifted (spec := spec) x y)
    ⦃⇓ r => ⌜r = x + y⌝⦄ := by
  mvcgen [addOrPanicLifted, addOrPanic]
```

With `@[spec] triple_liftRustM` registered in the `mvcgen` index,
`mvcgen` now peels the `liftRustM` boundary automatically, walks into
the `RustM` body of `addOrPanic`, and closes the residual vc in a
single tactic call.

The `[spec.Fintype] [spec.Inhabited]` constraints are inherited from
VCVio's `WP (OracleComp spec) .pure` and are the only additional
obligation the oracle layer imposes.

## Compositional boundary lemma

`triple_liftRustM` in `Bridge.lean` transports a hax-side `Triple`
through the lift in one step:

```lean
@[spec]
theorem triple_liftRustM [spec.Fintype] [spec.Inhabited]
    (x : RustM α)
    {Q : PostCond α (.except Interop.Rust.Error (.except PUnit .pure))}
    {P : Assertion (.except Interop.Rust.Error (.except PUnit .pure))}
    (h : Std.Do.Triple (ps := .except _root_.Error (.except PUnit .pure)) x P
          (Q.1, fun e => Q.2.1 (errorOfHax e), Q.2.2)) :
    Std.Do.Triple
      (liftRustM (spec := spec) x : Interop.Rust.RustOracleComp spec α)
      P Q
```

The only move from the hax-side post-condition is rebranding the error
handler: `Q.2.1 ∘ errorOfHax` instead of `Q.2.1`. The success handler
(`Q.1`) and divergence handler (`Q.2.2`) are shared verbatim, which
reflects that `liftRustM` is the identity on those cases modulo the
transformer encoding. This lemma is what lets us reuse hax's own
`@[spec]` library downstream without reproving lifts pointwise.

### `@[spec]` indexing

`triple_liftRustM` is tagged `@[spec]`, so hax's `hax_mvcgen` and
VCVio's `mvcgen` both index it automatically: whenever they encounter
a goal whose program starts with `liftRustM x`, they apply this lemma
and reduce the obligation to the hax-side `Triple` on `x`, shunting
the error-post through `errorOfHax`. In the concrete examples below
this means that `mvcgen [addOrPanicLifted, addOrPanic]` closes the
whole lifted Triple in one tactic call (see `Examples.lean`), and
`Computation.lean` / `Division.lean` / `Adc.lean` all transport their
respective hax-side specs to the oracle side in one line of proof.

### `LawfulMonadLift` / `MonadHom` statements

`liftRustM` is also bundled as a monad morphism in two equivalent
ways:

* `instLawfulMonadLiftRustM : LawfulMonadLift RustM (RustOracleComp spec)` —
  the typeclass form, picked up automatically by generic `liftM`
  lemmas.
* `liftRustMHom : RustM →ᵐ RustOracleComp spec` — the bundled
  `MonadHom` from `ToMathlib.Control.Monad.Hom`, which immediately
  gives `mmap_pure`, `mmap_bind`, `mmap_map`, `mmap_seq`, etc. on the
  lift. This is the mechanism by which arbitrary pure/bind-preserving
  properties transport across the bridge, not just Hoare triples:
  `triple_liftRustM` is one instantiation of the general pattern.

## Oracle-composed Triple spec

`oracleThenAdd_triple` in `Examples.lean` is the "genuine" boundary
example: a `RustOracleComp`-shaped `Triple` on a program that both
issues an oracle query and invokes a hax-style `RustM` function.

```lean
def oracleThenAdd (x : Nat) (t : ι) (coe : spec.Range t → Nat) :
    Interop.Rust.RustOracleComp spec Nat := do
  let y ← (liftM (query t) : OracleComp spec _)
  liftRustM (addOrPanic x (coe y))

theorem oracleThenAdd_triple (x : Nat) (t : ι) (coe : spec.Range t → Nat)
    [spec.Fintype] [spec.Inhabited]
    (hbound : ∀ y : spec.Range t, x + coe y < 2 ^ 32) :
    ⦃⌜True⌝⦄
    (oracleThenAdd (spec := spec) x t coe)
    ⦃⇓ r => ⌜x ≤ r⌝⦄
```

The proof is `mvcgen` + the `wpProp`-to-`support` bridge from VCVio's
`StdDoBridge` for the single oracle step, then `simp` closes the
lifted `RustM` tail. The oracle query is lifted through the derived
`MonadLiftT (OracleComp spec) (RustOracleComp spec)` chain
(`OptionT.lift` composed with `ExceptT.lift`), not a direct
`MonadLift` instance; keeping the chain derived ensures `mvcgen` can
peel it via the standard `Spec.monadLift_{OptionT,ExceptT}` rules
rather than short-circuiting on a hand-written instance.

## Real hax output: `Computation.lean`

`Interop/Hax/Computation.lean` is the first example where the `RustM`
side is not a hand-crafted toy but real hax output. The Rust source
comes from hax's test suite
(`tests/lean-tests/src/constants.rs`):

```rust
const fn computation(x: u32) -> u32 {
    x + x + 1
}
```

hax compiles it (verbatim, modulo the enclosing namespace) into the
`RustM` monad:

```lean
@[spec]
def computation (x : u32) : RustM u32 := do ((← (x +? x)) +? (1 : u32))
```

We reproduce the emitted definition, prove a `Std.Do` Triple on the
`RustM` side using hax's own `UInt32.haxAdd_spec`:

```lean
theorem computation_triple (x : u32) :
    ⦃⌜2 * x.toNat + 1 < 2 ^ 32⌝⦄
    (computation x)
    ⦃⇓ r => ⌜r.toNat = 2 * x.toNat + 1⌝⦄
```

and transport it to `RustOracleComp` in one step via the boundary
lemma:

```lean
theorem computationLifted_triple [spec.Fintype] [spec.Inhabited]
    (x : u32) :
    ⦃⌜2 * x.toNat + 1 < 2 ^ 32⌝⦄
    (computationLifted (spec := spec) x)
    ⦃⇓ r => ⌜r.toNat = 2 * x.toNat + 1⌝⦄ := by
  unfold computationLifted
  exact triple_liftRustM _ (computation_triple x)
```

This is the intended workflow: hax emits the function and its
`@[spec]` lemmas in the `RustM` / `Hax` world; we prove the hax-side
Triple with hax's tactics and spec library; `triple_liftRustM` moves
the result to the oracle-aware target without reproof. The
`errorOfHax` rebrand inside `triple_liftRustM` is invisible here
because the precondition rules out the panic branch.

## Second hax example: `Division.lean`

`Interop/Hax/Division.lean` complements `Computation.lean` by
exercising the `.divisionByZero` branch of `errorOfHax` end-to-end.
The Rust side is hax's own `/?` operator on `u32`, which reduces to
`if y = 0 then .fail .divisionByZero else pure (x / y)`:

```lean
@[spec]
def checkedDiv (x y : u32) : RustM u32 := x /? y

theorem checkedDiv_triple (x y : u32) (h : y ≠ 0) :
    ⦃⌜True⌝⦄ (checkedDiv x y) ⦃⇓ r => ⌜r.toNat = x.toNat / y.toNat⌝⦄ := by
  unfold checkedDiv
  exact UInt32.haxDiv_spec x y h

theorem checkedDivLifted_triple [spec.Fintype] [spec.Inhabited]
    (x y : u32) (h : y ≠ 0) :
    ⦃⌜True⌝⦄
    (checkedDivLifted (spec := spec) x y)
    ⦃⇓ r => ⌜r.toNat = x.toNat / y.toNat⌝⦄ := by
  unfold checkedDivLifted
  exact triple_liftRustM _ (checkedDiv_triple x y h)
```

Two further equality-level lemmas (`checkedDivLifted_ok_of_ne_zero`
and `checkedDivLifted_fail_of_zero`) directly witness the
`errorOfHax .divisionByZero = .divisionByZero` rebrand when the
precondition does not rule out the panic branch. This is the concrete
test that the `Error` translation preserves the constructor.

## Flagship hax example: `Adc.lean`

`Interop/Hax/Adc.lean` reproduces hax's own `lean_adc` demo inside
the bridge. The Rust source is

```rust
pub fn adc_u32(a: u32, b: u32, carry_in: u32) -> (u32, u32) {
    let wide: u64 = a as u64 + b as u64 + carry_in as u64;
    let sum: u32 = wide as u32;
    let carry_out: u32 = (wide >> 32u64) as u32;
    (sum, carry_out)
}
```

hax's `#[hax_lib::lean::after(...)]` attribute embeds the canonical
ADC Triple in the source; we reproduce it verbatim and close it with
hax's heavyweight proof stack:

```lean
set_option maxHeartbeats 1000000 in
set_option hax_mvcgen.specset "bv" in
theorem adc_u32_spec (a b carry_in : u32) :
    ⦃⌜carry_in ≤ 1⌝⦄
    adc_u32 a b carry_in
    ⦃⇓ ⟨sum, carry_out⟩ =>
      ⌜carry_out ≤ 1 ∧
        UInt32.toUInt64 a + UInt32.toUInt64 b + UInt32.toUInt64 carry_in =
          UInt32.toUInt64 sum + (UInt32.toUInt64 carry_out <<< (32 : UInt64))⌝⦄ := by
  hax_mvcgen [adc_u32]
    <;> bv_decide (timeout := 90)
```

Transport to `RustOracleComp` is still one line:

```lean
theorem adc_u32_Lifted_spec [spec.Fintype] [spec.Inhabited]
    (a b carry_in : u32) :
    ⦃⌜carry_in ≤ 1⌝⦄
    (adc_u32_Lifted (spec := spec) a b carry_in)
    ⦃⇓ ⟨sum, carry_out⟩ =>
      ⌜carry_out ≤ 1 ∧
        UInt32.toUInt64 a + UInt32.toUInt64 b + UInt32.toUInt64 carry_in =
          UInt32.toUInt64 sum + (UInt32.toUInt64 carry_out <<< (32 : UInt64))⌝⦄ := by
  unfold adc_u32_Lifted
  exact triple_liftRustM _ (adc_u32_spec a b carry_in)
```

This is the full intended workflow: a real hax-emitted function,
a bit-blasted proof closed entirely by `hax_mvcgen <;> bv_decide`, and
a one-line transport to the oracle-aware target.

## First lattice-crypto primitive: `Barrett.lean`

`Interop/Hax/Barrett.lean` is the first hax example in the bridge that
is actually used in production lattice cryptography. The Rust source
is hax's `examples/lean_barrett/src/lib.rs`:

```rust
pub(crate) type FieldElement = i32;

const BARRETT_R: i64 = 0x400000;
const BARRETT_SHIFT: i64 = 26;
const BARRETT_MULTIPLIER: i64 = 20159;
pub(crate) const FIELD_MODULUS: i32 = 3329;

pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
```

This is the *modular reduction by `q = 3329`* used by ML-KEM / Kyber on
every polynomial coefficient; the same routine, with `q = 8380417`, is
used by ML-DSA. It is the smallest piece of lattice cryptography that
is both self-contained and realistic.

### Hax-side spec: `hax_bv_decide`

The `RustM` function is a five-op chain of checked arithmetic
(`*? / +? / -? / >>>?`) with two cross-width casts via
`rust_primitives.hax.cast_op`. We state the standard Barrett window
property directly on signed machine integers (no `.toInt`-style
lifting, which would turn the goal into a mixed `Int`/`BitVec`
problem that `bv_decide` cannot close) and let hax's upstream bit-
blasting stack do all the work:

```lean
set_option maxHeartbeats 1_000_000 in
theorem barrett_reduce_spec (value : i32) :
    ⦃⌜value.toInt64 ≥ -(4194304 : Int64) ∧
       value.toInt64 ≤ (4194304 : Int64)⌝⦄
    (barrett_reduce value)
    ⦃⇓ r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32) ∧
      (r = value % (3329 : Int32) ∨
       r = value % (3329 : Int32) + (3329 : Int32) ∨
       r = value % (3329 : Int32) - (3329 : Int32))⌝⦄ := by
  unfold barrett_reduce FIELD_MODULUS BARRETT_R
    BARRETT_MULTIPLIER BARRETT_SHIFT
  hax_bv_decide (timeout := 90)
```

The precondition `|value| ≤ BARRETT_R = 2^22` holds on every
coefficient ML-KEM / ML-DSA ever passes through Barrett. The
post-condition is the canonical window property: `r` is in the
representative set `(-q, q)` and is congruent to `value` modulo `q`.
The three disjuncts spell out the signed representative rather than
hiding behind a single `mod` operator, because that form is what
`bv_decide` can mechanically check at the bit level.

Unfolding `FIELD_MODULUS` in the proof is required: without it,
`bv_decide` treats it as an opaque constant and fails with an
abstraction warning.

### One-line transport to `RustOracleComp`

```lean
def barrett_reduce_Lifted (value : i32) :
    Interop.Rust.RustOracleComp spec i32 :=
  liftRustM (barrett_reduce value)

theorem barrett_reduce_Lifted_spec [spec.Fintype] [spec.Inhabited]
    (value : i32) :
    ⦃⌜value.toInt64 ≥ -(4194304 : Int64) ∧
       value.toInt64 ≤ (4194304 : Int64)⌝⦄
    (barrett_reduce_Lifted (spec := spec) value)
    ⦃⇓ r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32) ∧
      (r = value % (3329 : Int32) ∨
       r = value % (3329 : Int32) + (3329 : Int32) ∨
       r = value % (3329 : Int32) - (3329 : Int32))⌝⦄ := by
  unfold barrett_reduce_Lifted
  exact triple_liftRustM _ (barrett_reduce_spec value)
```

### Oracle composition: `oracleThenBarrett`

The minimum demonstration that `RustOracleComp` composes a lifted
lattice primitive with a real oracle query:

```lean
def oracleThenBarrett (t : ι) (coe : spec.Range t → i32) :
    Interop.Rust.RustOracleComp spec i32 := do
  let y ← (liftM (query t) : OracleComp spec _)
  barrett_reduce_Lifted (coe y)

theorem oracleThenBarrett_triple
    [spec.Fintype] [spec.Inhabited]
    (t : ι) (coe : spec.Range t → i32)
    (hbound : ∀ y : spec.Range t,
      (coe y).toInt64 ≥ -(4194304 : Int64) ∧
      (coe y).toInt64 ≤ (4194304 : Int64)) :
    ⦃⌜True⌝⦄
    (oracleThenBarrett (spec := spec) t coe)
    ⦃⇓ r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32)⌝⦄
```

The proof is `mvcgen` + the `wpProp_iff_forall_support` bridge for the
single oracle step, then `Triple.entails_wp_of_post` weakens
`barrett_reduce_Lifted_spec`'s postcondition to the window property
alone (the modular-equivalence disjunct is dropped because it mentions
the oracle outcome `y`). This is exactly the shape you would need to
verify an ML-KEM coefficient-sampling loop: an oracle draws noise,
Barrett reduces it, the result stays in the field.

## Probabilistic spec: genuine VCVio-side content

Every spec above is a `Std.Do.Triple`, which is universal over oracle
outcomes and contains no probabilistic content; effectively we have
just been wrapping the `RustM` spec. The payoff of dropping `Hax.RustM`
into `Interop.Rust.RustOracleComp` is that the underlying `OracleComp`
layer carries `HasEvalSPMF` (via the `ExceptT` and `OptionT` instances
in `VCVio.EvalDist.Instances.{ErrorT,OptionT}`), so claims like
`Pr[panic] = 1/2` become well-defined and provable. Those claims
cannot be stated at the hax level: `Hax.RustM` has no oracle to sample
at all, and the `Triple` layer has no way to talk about probability.

`Examples.lean` closes the loop with a minimal probabilistic harness,
`tossedAdd`, that flips a uniform bit `b ∈ Fin 2` from `unifSpec`, then
dispatches to either `addOrPanicLifted 0 0` (always returns `0`) or
`addOrPanicLifted (2^32) 0` (always overflows):

```lean
def tossedAdd : Interop.Rust.RustOracleComp unifSpec Nat := do
  let b ← ($[0..1] : ProbComp (Fin 2))
  if b = 0 then addOrPanicLifted 0 0
  else addOrPanicLifted (2 ^ 32) 0
```

The proof is driven by a transformer-stack peel that exposes the
canonical `OracleComp spec (Option (Except ε α))` form,

```lean
theorem tossedAdd_run_run :
    tossedAdd.run.run =
      ($[0..1] >>= fun b : Fin 2 =>
        pure (some (if b = 0 then
          (Except.ok 0 : Except Interop.Rust.Error Nat)
          else Except.error .integerOverflow)) :
            OracleComp unifSpec (Option (Except Interop.Rust.Error Nat)))
```

after which the panic probability follows by a one-liner sum over
`Fin 2` using `HasEvalSPMF.probOutput_bind_eq_sum_fintype` and
`ProbComp.probOutput_uniformFin`:

```lean
theorem tossedAdd_panic_prob :
    Pr[= some (Except.error Interop.Rust.Error.integerOverflow) |
        tossedAdd.run.run] = 2⁻¹
```

The peel lemma is the reusable piece: once a `RustOracleComp` program
reaches the form `($sample) >>= fun x => pure (some (.ok _ / .error
_))`, every `Pr[=]`, `support`, and `evalDist` lemma in VCVio applies
without detour through the transformer stack.

## Risks

- `_root_.Error` (hax) is namespace-collision-prone with anything else
  that defines a root-level `Error`. The mirrored `Interop.Rust.Error`
  is in its own namespace; rebranding happens at the boundary via
  `errorOfHax`, not throughout.
- Hax tactics (`Hax.Tactic.HaxMvcgen`) and the global `@[spec]`
  `DiscrTree` may interact with VCVio's `mvcgen`. If that becomes
  visible, quarantine hax tactic imports to `Interop/Hax/**` and keep
  `Interop.Hax.Bridge` tactic-free.
- See `docs/agents/interop.md` for the full risk list.

## Completed follow-ups

The previous round of TODOs (as of PR #292) is now resolved:

- `triple_liftRustM` is `@[spec]`-tagged; `mvcgen` auto-applies it,
  collapsing `addOrPanicLifted_triple` to a one-tactic proof and
  reducing every downstream `*_Lifted_spec` to
  `triple_liftRustM _ (hax_side_spec …)`.
- `Division.lean` exercises the `.divisionByZero` constructor of
  `errorOfHax` end-to-end, both at the Triple level and via the
  equality-level `checkedDivLifted_fail_of_zero` witness.
- `Adc.lean` runs `hax_mvcgen [..] <;> bv_decide` on the canonical
  `adc_u32` ADC function and transports the result over the bridge.
- `liftRustM` is bundled as a `LawfulMonadLift` instance and a
  `MonadHom` (`liftRustMHom`), so any monad-morphism-indexed property
  (`mmap_pure`, `mmap_bind`, `mmap_map`, `mmap_seq`, …) transports
  automatically across the lift — not just Hoare triples.
- The `tossedAdd_run_run` proof idiom is generalized into reusable
  `@[simp]` peel lemmas in `Interop/Rust/Run.lean`
  (`run_run_bind_liftM`, `run_run_liftM`, `run_run_pure`,
  `run_run_throw`, `run_run_div`, `run_run_fail`, `run_run_ok`), which
  drive the probabilistic proofs in both `Examples.lean` and
  `Division.lean`.

## Remaining open questions

- A probabilistic hax-side spec library does not exist yet, so the
  `MonadHom` is currently used only structurally. If hax ever ships a
  `Pr[_]`-style spec layer, `mmap_pure` / `mmap_bind` on
  `liftRustMHom` will transport those specs without any additional
  infrastructure.
- `Adc.lean` and `Barrett.lean` both bump `maxHeartbeats` to 1M;
  reducing this (e.g. by a more targeted specset than `"bv"`) is a
  worthwhile but non-urgent optimization.
- A genuinely oracle-using hax function (e.g. a randomized
  construction compiled by hax) remains the natural next milestone:
  every hax example we can currently find is deterministic.

## Lattice-crypto outlook

`Barrett.lean` is the first real lattice-crypto primitive in the
bridge. The natural next targets, in rough order of effort:

### Plausible next: the rest of the `lean_barrett` surface

hax's `examples/lean_barrett` is not just `barrett_reduce`; it also
ships `montgomery_reduce`, `fe_add`, `fe_sub`, NTT helpers, and a
polynomial wrapper. All of these have the same proof shape:
`hax_bv_decide`-provable on the `RustM` side, transported by one
line of `triple_liftRustM`. Adding them is a matter of
transcription; the proof technique does not need to change.

### Medium lift: ML-KEM inner loop

The ML-KEM key generation / encryption / decryption pipeline at the
coefficient level is: sample from a distribution → NTT → pointwise
multiply → inverse NTT → compress/decompress, where every
coefficient-level operation bottoms out at a `barrett_reduce` or
`montgomery_reduce` call. Lifting the full pipeline to
`RustOracleComp` needs:

1. A polynomial representation (`Vector i32 256`) and its NTT /
   inverse-NTT routines with `hax_bv_decide` specs.
2. A sampler lifted from an oracle (the Kyber spec's
   `SampleNTT` / `SamplePolyCBD`), which is the first hax example
   that genuinely uses the `OracleComp` layer rather than just
   sitting on top of it.
3. A compositional `Triple` spec tying the pipeline together.

`hax` has a partial port of this pipeline in its `proofs/` tree
(`libcrux-ml-kem`), but as of hax `main@492a34e3` it is not wired
into `examples/`. The proof cost is dominated by the NTT (256
coefficients, one `barrett_reduce` per multiplication), but every
step is a `bv_decide`-sized obligation. Realistic budget: multiple
weeks of focused work, most of it driven by hax's upstream proof
stack.

### Falcon: why this is infeasible right now

Falcon (FIPS 206) is structurally harder than ML-KEM / ML-DSA:

- Falcon's signing is *floating-point*. Pornin's reference C
  implementation (`falcon-impl`) uses IEEE-754 double precision
  for FFT-based trapdoor sampling (`ffSampling`). Neither hax nor
  VCVio have a verified IEEE-754 story; hax's `lean` backend emits
  `f64` as an opaque type with no `bv_decide`-style automation.
- Falcon's security proof relies on *discrete Gaussian sampling*,
  which VCVio has a partial spec for (`LatticeCrypto/
  DiscreteGaussian.lean`) but which is not yet tied to a
  constant-time Rust implementation.
- The published Rust port of Falcon (`pornin/falcon-rs`) is a
  translation of the C reference and shares the floating-point
  dependency. `hax` cannot currently extract it.

A realistic path is *post-Falcon*: wait for a Rust port of a
lattice signature scheme that avoids floating point entirely
(e.g. HAWK, FN-DSA in its "G+G" form, or a future revision of
Falcon based on integer FFT), then reuse the Barrett-style
bit-blasting proofs. Until then, ML-KEM / ML-DSA (Kyber /
Dilithium) are the realistic targets.

### Rough order of operations

1. ~~`barrett_reduce` port (this PR)~~.
2. Complete the `lean_barrett` example (other `fe_*` operations,
   NTT helpers). Low proof risk, still `bv_decide`-sized.
3. Lift a genuinely randomized hax function (e.g. `SamplePolyCBD`
   from libcrux-ml-kem) to exercise the `OracleComp` layer for
   real.
4. Scale up to a full ML-KEM / ML-DSA pipeline spec, with
   coefficient-level correctness (per-Barrett) composed into a
   polynomial-level correctness theorem.
5. Revisit Falcon when a floating-point-free lattice signature
   scheme is Rust-available.
