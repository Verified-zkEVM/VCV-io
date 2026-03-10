# Task: Fill sorry's in `VCVio/CryptoFoundations/FiatShamir.lean` (Fiat-Shamir security)

**Wave**: 2 (after wave 1 merges; depends on Schnorr properties from prompt 10)
**Difficulty**: Hard
**Sorry count**: 2 (1 straightforward, 1 research-tier)

## CRITICAL CONSTRAINT — READ BEFORE DOING ANYTHING

**You MUST NOT change any `def`, `noncomputable def`, `abbrev`, or `class` definition.**
**You MUST NOT change any theorem/lemma signature (name, type, or hypotheses).**
**You MUST NOT add new hypotheses to existing theorems.**
**You MUST NOT modify any file other than `VCVio/CryptoFoundations/FiatShamir.lean`.**
**You MUST NOT modify upstream/shared library files**.

The ONLY things you may do:
1. Replace `sorry` with a valid proof term.
2. Add `private` helper lemmas in the target file, marked with `-- TODO: move to <destination>`.

**SPECIAL NOTE on `euf_cma_bound`**: The RHS of the inequality (line ~93) is itself `sorry` — meaning the concrete bound expression has not been specified yet. You must determine the correct bound from the forking lemma and fill in BOTH the bound expression AND the proof. If you cannot determine the correct bound, leave both sorry's in place and document your analysis.

If you cannot prove a theorem as stated, **leave the `sorry` in place** and
document what you tried and what blocked you in a `/- ... -/` comment block
adjacent to the sorry.

## Worktree setup

```bash
./scripts/setup-worktree.sh ../vcv-11-fiat-shamir <branch>
cd ../vcv-11-fiat-shamir
```

## Critical Lean 4 / VCVio gotchas

- `set_option autoImplicit false` is project-wide.
- `[spec.Fintype]` and `[spec.Inhabited]` required for `evalDist`.
- `$ᵗ T` requires `SampleableType T`.
- `++ₒ` is dead — use `+` for combining OracleSpecs.
- The `FiatShamir` structure uses `unifSpec + (M × PC →ₒ Ω)` as its oracle spec.
- `SignatureAlg.PerfectlyComplete` is defined in `SignatureAlg.lean`, NOT `SigmaAlg.lean`.

## Scope: YOUR 2 sorry's

| # | Lemma | Line | Signature summary |
|---|-------|------|-------------------|
| 1 | `perfectlyCorrect` | ~82 | `σ.PerfectlyComplete → SignatureAlg.PerfectlyComplete (FiatShamir σ hr M)` |
| 2 | `euf_cma_bound` | ~88 | `adv.advantage ≤ <bound>` (bound itself is `sorry`) |

## Target file (reference snapshot — lines 71-96)

Always read the actual file on disk for ground truth.

```lean
namespace FiatShamir

variable {X W PC SC Ω P : Type} {p : X → W → Bool}
  [SampleableType X] [SampleableType W]
  [DecidableEq PC] [DecidableEq P] [DecidableEq Ω] [SampleableType Ω]

variable (σ : SigmaAlg X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (M : Type) [DecidableEq M]

theorem perfectlyCorrect (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete (FiatShamir σ hr M) := by
  sorry

theorem euf_cma_bound
    (hss : σ.SpeciallySound)
    (adv : SignatureAlg.unforgeableAdv (FiatShamir σ hr M))
    (qBound : ℕ) :
    adv.advantage ≤
      sorry := by
  sorry

end FiatShamir
```

## Key API

### From `VCVio/CryptoFoundations/SignatureAlg.lean`

```lean
def SignatureAlg.PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S) : Prop :=
  ∀ msg : M, Pr[= true | sigAlg.exec do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig] = 1
```

### From `VCVio/CryptoFoundations/SigmaAlg.lean`

```lean
def SigmaAlg.PerfectlyComplete (σ : SigmaAlg S W PC SC Ω P p) : Prop :=
  ∀ x w, p x w = true →
    Pr[= true | do
      let (pc, sc) ← σ.commit x w
      let ω ← $ᵗ Ω
      let π ← σ.respond x w sc ω
      return σ.verify x pc ω π] = 1
```

### From `FiatShamir` definition (same file, lines 35-54)

```lean
def FiatShamir ... : SignatureAlg ... where
  keygen := hr.gen                    -- generates (pk, sk) = (x, w) satisfying p
  sign pk sk m := do
    let (c, e) ← σ.commit pk sk
    let r ← query (spec := unifSpec + (M × PC →ₒ Ω)) (Sum.inr (m, c))
    let s ← σ.respond pk sk e r
    return (c, s)
  verify pk m (c, s) := do
    let r' ← query (spec := unifSpec + (M × PC →ₒ Ω)) (Sum.inr (m, c))
    return σ.verify pk c r' s
  exec comp := StateT.run' (simulateQ (idImpl + randomOracle) comp) ∅
```

### From `VCVio/CryptoFoundations/Fork.lean`

```lean
def fork (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α))
```

## Proof strategy hints

### 1. `perfectlyCorrect`

**Strategy**: Unfold `SignatureAlg.PerfectlyComplete` for `FiatShamir σ hr M`. For any message `msg`:
1. `keygen` generates `(pk, sk)` via `hr.gen`, which satisfies `p pk sk = true` (by `hr.gen_sound`).
2. `sign pk sk msg` commits, queries the random oracle for `r`, responds with `σ.respond`.
3. `verify pk msg (c, s)` re-queries the random oracle for the same `(msg, c)`. Since the random oracle is deterministic (cached), it returns the same `r`. Then checks `σ.verify pk c r s`.
4. By `hc` (sigma protocol completeness), `σ.verify pk c r (σ.respond pk sk sc r) = true` with probability 1.

The key technical step is showing the random oracle returns the same value on the same input (caching behavior). The `exec` field uses `StateT ... randomOracle` which caches queries.

### 2. `euf_cma_bound`

**Strategy**: This is the EUF-CMA security reduction via the forking lemma. The standard approach:
1. Given a forger `adv` that succeeds with advantage `ε`, fork it to get two accepting transcripts.
2. By special soundness, extract a witness from two transcripts with different challenges.
3. The forking lemma gives a lower bound on the forking success probability.

The bound should be something like: `ε * (ε / (qBound + 1) - 1 / card Ω)` from the general forking lemma. But `CryptoFoundations/Fork.lean` has its own sorry's, so this may not be fully provable yet. **If blocked by upstream sorry's, document and leave in place.**

## Build & verify

```bash
lake build VCVio.CryptoFoundations.FiatShamir
```

## Exit criteria

Return when:
- (a) Both sorry's are replaced with complete proofs (including the bound expression). `lake build` succeeds. OR
- (b) You resolve `perfectlyCorrect` and document precisely why `euf_cma_bound` is blocked (expected — upstream forking lemma has sorry's). OR
- (c) You hit a fundamental blocker on both. Document precisely.

**Verification**: Run `git diff` before returning. Confirm NO changes to any
`def`, `noncomputable def`, `abbrev`, or theorem/lemma signature lines
(except for the `sorry` on line ~93 which IS part of the expression to fill in).

## Dependency note

- `perfectlyCorrect` depends on `SigmaAlg.PerfectlyComplete` (definition, no sorry), random oracle caching semantics, and `GenerableRelation` properties. Should be self-contained.
- `euf_cma_bound` depends on the forking lemma from `CryptoFoundations/Fork.lean` which has pre-existing sorry's. This may block the proof.
