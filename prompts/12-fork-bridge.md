# Task: Fill sorry in `VCVio/ProgramLogic/Fork.lean` (triple_fork)

**Wave**: 2 (after wave 1 merges)
**Difficulty**: Hard (research-tier — may be blocked by upstream sorry's)
**Sorry count**: 1

## CRITICAL CONSTRAINT — READ BEFORE DOING ANYTHING

**You MUST NOT change any `def`, `noncomputable def`, `abbrev`, or `class` definition.**
**You MUST NOT change any theorem/lemma signature (name, type, or hypotheses).**
**You MUST NOT add new hypotheses to existing theorems.**
**You MUST NOT modify any file other than `VCVio/ProgramLogic/Fork.lean`.**
**You MUST NOT modify upstream/shared library files**.

The ONLY things you may do:
1. Replace `sorry` with a valid proof term.
2. Add `private` helper lemmas in the target file, marked with `-- TODO: move to <destination>`.

If you cannot prove a theorem as stated, **leave the `sorry` in place** and
document what you tried and what blocked you in a `/- ... -/` comment block
adjacent to the sorry. In particular, if the upstream `CryptoFoundations/Fork.lean`
lacks a needed lemma (it has sorry's), document which lemma is missing and what
its statement should be.

## Worktree setup

```bash
./scripts/setup-worktree.sh ../vcv-12-fork-bridge <branch>
cd ../vcv-12-fork-bridge
```

## Critical Lean 4 / VCVio gotchas

- `set_option autoImplicit false` is project-wide.
- `[spec.Fintype]` and `[spec.Inhabited]` required for `evalDist`.
- `OracleComp.inductionOn` is the canonical eliminator.
- `CryptoFoundations/Fork.lean` has pre-existing sorry's — some lemmas you need may not be proved yet.

## Scope: YOUR 1 sorry only

| # | Lemma | Line | Signature summary |
|---|-------|------|-------------------|
| 1 | `triple_fork` | ~32 | Forking lemma as a quantitative Hoare triple |

## Target file (reference snapshot)

Always read the actual file on disk for ground truth.

```lean
-- File: VCVio/ProgramLogic/Fork.lean
import VCVio.CryptoFoundations.Fork
import VCVio.ProgramLogic.Unary.HoareTriple

set_option autoImplicit false

open OracleSpec OracleComp ENNReal

namespace OracleComp.ProgramLogic

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α : Type}

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec]

theorem triple_fork (post : α × α → ℝ≥0∞) :
    Triple (spec := spec)
      (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
       let h : ℝ≥0∞ := Fintype.card (spec.Range i)
       let q := qb i + 1
       acc * (acc / q - h⁻¹))
      (fork main qb js i cf)
      (fun r => match r with | some p => post p | none => 0) := by
  sorry

end OracleComp.ProgramLogic
```

## Key API

### From `VCVio/CryptoFoundations/Fork.lean`

```lean
def fork (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α))

-- The main forking lemma bound (may have sorry's upstream):
-- Look for lemmas like `fork_success_bound` or `probOutput_fork` that give
-- a lower bound on Pr[some (x₁, x₂) | fork ...] in terms of acceptance probability.
```

### From `VCVio/ProgramLogic/Unary/HoareTriple.lean`

```lean
noncomputable abbrev Triple (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) : Prop :=
  MAlgOrdered.Triple (m := OracleComp spec) (l := ℝ≥0∞) pre oa post

-- Unfolds to: pre ≤ wp oa post = ∑' x, Pr[= x | oa] * post x

theorem triple_conseq {pre pre' : ℝ≥0∞} {oa : OracleComp spec α}
    {post post' : α → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ x, post x ≤ post' x) :
    Triple pre oa post → Triple pre' oa post'
```

## Proof strategy hints

### 1. `triple_fork`

**Strategy**: The `Triple` unfolds to `pre ≤ wp (fork ...) post`, which is `pre ≤ ∑' x, Pr[= x | fork ...] * post x`.

The `none` case contributes 0 (by the `match` in `post`), so the sum reduces to:
`∑' p, Pr[= some p | fork ...] * post p`.

The precondition `acc * (acc / q - h⁻¹)` is the forking lemma's lower bound on `Pr[some _ | fork ...]`.

To prove this, you need:
1. A lemma from `CryptoFoundations/Fork.lean` that gives `acc * (acc / q - h⁻¹) ≤ Pr[some _ | fork ...]` (or equivalently, `Pr[none | fork ...] ≤ 1 - acc * (acc / q - h⁻¹)`).
2. Then: `pre ≤ Pr[some _ | fork ...] ≤ ∑' p, Pr[= some p | fork ...] * 1 ≤ ∑' p, Pr[= some p | fork ...] * post p` (if `post p ≥ 1` for all `p`, or use a different argument).

**HOWEVER**: This strategy only works if `post p ≥ 1` for all `p`, which is not assumed. The actual bridge may require `post` to be the constant 1 function on `some` outputs, or the theorem statement may need revision.

**Alternative**: If the upstream forking lemma gives `Pr[some _ | fork ...] ≥ pre`, then use `triple_conseq` with a coarser postcondition.

**Important**: Explore `CryptoFoundations/Fork.lean` to find what probability bounds are available. Many may be sorry'd. Document what you find.

## Build & verify

```bash
lake build VCVio.ProgramLogic.Fork
```

## Exit criteria

Return when:
- (a) The sorry is replaced with a complete proof. `lake build` succeeds. OR
- (b) You document precisely which upstream lemma from `CryptoFoundations/Fork.lean` is needed but sorry'd, what its statement should be, and how the proof would proceed given that lemma. This is the EXPECTED outcome for this prompt.

**Verification**: Run `git diff` before returning. Confirm NO changes to any
`def`, `noncomputable def`, `abbrev`, or theorem/lemma signature lines.

## Dependency note

This proof critically depends on probability bounds from `CryptoFoundations/Fork.lean`, which has pre-existing sorry's. The main goal of this prompt is either to complete the proof if the needed lemmas exist, or to document precisely what's missing for future work.
