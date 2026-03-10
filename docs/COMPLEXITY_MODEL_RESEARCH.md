# Complexity & Runtime Modeling Research

Research synthesis for VCV-io's cost/complexity/PPT infrastructure.
Produced via multi-agent council analysis (Mar 8, 2026).

## References Investigated

- **EasyCrypt** (local clone): `theories/query_counting/OracleBounds.ec`, `ehoare` logic
- **Barbosa, Barthe et al. CCS 2021**: "Mechanized Proofs of Adversarial Complexity and Application to Universal Composability" ([ePrint 2021/156](https://eprint.iacr.org/2021/156))
- **CALF** (Cost-Aware Logical Framework): Niu, Sterling, Grodin, Harper (POPL 2022)
- **Decalf**: Grodin et al. (POPL 2024) — extends CALF to probabilistic effects
- **Polytime-Formalizations**: [ianm1129/Polytime-Formalizations](https://github.com/ianm1129/Polytime-Formalizations) — WIP Lean 4 port of CALF ideas, imports VCVio
- **CSLib**: [leanprover/cslib](https://github.com/leanprover/cslib) — `TimeM` cost-tracking monad, `Computability/` module
- **Kaminski et al.**: "Weakest Precondition Reasoning for Expected Runtimes" (ESOP 2016 / JACM 2018)

## Current VCV-io Infrastructure

| Component | Status | File |
|-----------|--------|------|
| `Negligible.lean` (~31 lines) | Working, dormant — thin wrapper over `SuperpolynomialDecay` | `VCVio/CryptoFoundations/Asymptotics/Negligible.lean` |
| `PolyTimeOC.lean` (~42 lines) | Entirely commented out, depends on unusable Mathlib TM infrastructure | `VCVio/CryptoFoundations/Asymptotics/PolyTimeOC.lean` |
| `SecExp` / `BoundedAdversary` | Concrete (non-asymptotic), no security parameter | `VCVio/CryptoFoundations/SecExp.lean` |
| `advantage₂` + triangle + game-hopping | Complete, non-asymptotic | `VCVio/CryptoFoundations/SecExp.lean` |
| `IsQueryBound` / `IsPerIndexQueryBound` | Working, concrete query-count bounds | `VCVio/OracleComp/QueryTracking/QueryBound.lean` |
| `costOracle` / `WriterT` cost tracking | Implemented, proven sound | `VCVio/OracleComp/QueryTracking/CountingOracle.lean` |
| `wp` (weakest preexpectation) | Working, `ℝ≥0∞`-valued, IS Kaminski's ert transformer | `VCVio/ProgramLogic/Unary/HoareTriple.lean` |
| Asymptotic `SecExp` (parameterized by `ℕ`) | Does not exist | — |
| `PPTAdversary` | Does not exist | — |

## Key Insight: wp IS Expected Cost

VCV-io's existing `wp` already computes expectations:

```
wp oa post = ∑' x, Pr[= x | oa] * post x
```

Setting `post := cost_function` yields expected cost with zero new machinery.
Tail bounds via Markov inequality are a one-lemma consequence of existing infrastructure.

## Consensus Findings

### 1. WriterT/costOracle Is the Right Mechanism

Five of six council agents converged: the `WriterT`/`costOracle` approach requires zero
changes to `OracleComp`, composes with `simulateQ` by construction, and enables
distributional reasoning through existing `wp`/`evalDist`. ~80% of infrastructure exists.

**Why not CALF-style MonadStep?** Adding a `step` constructor to `OracleComp = PFunctor.FreeM`
would cascade-break all induction principles, `simulateQ`, `evalDist`, `wp`, and both
program logics. The `WriterT`/`costOracle` mechanism achieves the same expressiveness
without touching the core type.

### 2. Query Bounds and Cost Monad Are Complementary

- `IsQueryBound` / `IsPerIndexQueryBound`: worst-case structural arguments
- `costOracle`: distributional / expected-case arguments
- `counting_bounded` theorem already bridges them
- Both should coexist

### 3. EasyCrypt's Three-Way Query Bound Equivalence

EasyCrypt proves three equivalent characterizations of "A makes at most q queries":

1. **Penalty**: `Pr[event ∧ count ≤ q]` relates to `Pr[event]`
2. **Enforcement**: Oracle drops queries beyond `q` (`Bounder` wrapper)
3. **Bounded**: Structural predicate (like `IsQueryBound`)

VCV-io should prove these equivalent once, then let users pick per proof.

### 4. VCV-io's wp = EasyCrypt's ehoare = Kaminski's ert

All express the same mathematics: `E[post(result)] ≤ pre`. The bridge
`byehoare` (EasyCrypt) = Markov inequality: `Pr[bad] ≤ E[potential] / threshold`.

## Recommended Architecture: Option A (Layered)

### Layer 1 — Security Statements (PPT = PolyQueries)

```lean
def PolyQueries (family : ℕ → OracleComp spec α) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, TotalQueryUpperBound (family n) (p.eval n)
```

Used in theorem statements: `∀ A, PolyQueries A → negligible (fun n => advantage n A)`

### Layer 2 — Cost Analysis (for constructions, extractors)

```lean
structure CostModel (spec : OracleSpec ι) where
  queryCost : spec.Domain → ℕ

def costDist (oa : OracleComp spec α) (cm : CostModel spec) :
    OracleComp spec (α × ℕ) :=
  (simulateQ (costOracle cm.queryCost) oa).run

noncomputable def expectedCost (oa : OracleComp spec α) (cm : CostModel spec) : ℝ≥0∞ :=
  wp (costDist oa cm) (fun (_, c) => ↑c)

def ExpectedPolyTime (family : ℕ → OracleComp spec α) (cm : CostModel spec) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, expectedCost (family n) cm ≤ p.eval n
```

### Bridge Lemmas

- `WorstCasePolyTime → PolyQueries` (each query costs ≥ 1)
- Markov: `Pr[cost > t | oa] ≤ expectedCost oa cm / t`
- Expected-PPT → strict-PPT with overwhelming probability

### Distributional Reasoning Tools

- `expectedCost` via `wp`
- `Pr[cost > t]` via `probEvent` on the cost distribution
- Markov inequality bridge
- Following Decalf: cost distribution is itself a computation, `evalDist` gives the cost PMF

## Recommended Architecture: Concrete ↔ Asymptotic

**Asymptotic wraps Concrete**: `SecurityExp` = `ℕ → SecExp ProbComp`

```lean
structure SecurityExp where
  experiment : ℕ → SecExp ProbComp

noncomputable def SecurityExp.advantage (exp : SecurityExp) : ℕ → ℝ≥0∞ :=
  fun n => (exp.experiment n).advantage

def SecurityExp.secure (exp : SecurityExp) : Prop :=
  negligible exp.advantage
```

Concrete proofs are immediately useful in asymptotic setting via pointwise bounds.

## Open Questions

1. **Should `CostModel.queryCost` be deterministic or probabilistic?**
   Deterministic is simpler. EasyCrypt uses deterministic.

2. **Internal computation cost (between queries)?**
   The cost monad only counts what you instrument. For oracle queries, automatic via
   `costOracle`. For internal pure computation, manual annotation needed.

3. **Variance and higher moments.**
   `wp` over `ℝ≥0∞` lacks subtraction, making variance awkward. Expected cost +
   Markov tail bounds may suffice; Chebyshev/Chernoff would need `ℝ`-valued layer.

4. **CSLib compatibility.** (See detailed section below.)

---

## CSLib Compatibility Analysis (Mar 8, 2026)

### CSLib Overview

[CSLib](https://github.com/leanprover/cslib) is the Lean Computer Science Library.
Local clone at `/Users/quang.dao/Documents/Lean/cslib/`.

### Relevant In-Flight PRs

| PR | Title | Status | Relevance |
|----|-------|--------|-----------|
| #404 | Cryptographic protocols and security definitions | DRAFT | **Critical** — parallel crypto framework |
| #401 | Query complexity framework with sorting examples | DRAFT | **High** — query cost model for algorithms |
| #400 | Complexity theory (P/NP/PSPACE) | CLOSED | Author moved to separate `complexitylib` repo |
| #396 | Remove h_mono from PolyTimeComputable.comp | OPEN | `PolyTimeComputable` on single-tape TMs |
| #372 | Query complexity model for algorithms theory | OPEN | **High** — competing query cost model |
| #370 | LongestCommonSublist: TimeM proof | OPEN | TimeM usage example |
| #360 | Additive writer monad (`AddWriterT`) | OPEN | Directly relevant to VCV-io's `WriterT` |
| #357 | Generalize TimeM to arbitrary cost types | MERGED | `TimeM` now uses `[AddMonoid T]` |

### PR #404: Crypto Framework (SamuelSchlesinger)

A 12K-line draft building a parallel crypto framework. Key differences from VCV-io:

- **No monadic oracle computation**: Uses `OracleInteraction Q R A` (fuel-bounded free monad
  with deterministic `run`), not VCV-io's `OracleComp`/`evalDist`/`PMF` denotational semantics.
- **Probability via `uniformExpect`**: Pre-samples randomness into a "coin space" product type,
  uses `uniformExpect` over `Fintype` in `ℝ`. VCV-io uses monadic composition + `evalDist`.
- **TM-backed polytime**: `PolyTimeEncodable`, `IsPolyTimeDistinguisher` — tied to TMs.
- **Complete proofs**: General Bellare-Neven Forking Lemma (525 lines), Fiat-Shamir ROM
  EUF-CMA reduction (3,107 lines), Schnorr completeness + HVZK + soundness.
- **Primitives**: `EncryptionScheme`, `PKEncryptionScheme`, `CommitmentScheme`, `HashFunction`,
  `MAC`, `OneWayFunction`, `PRF`, `PRG`, `Signature`, `SigmaProtocol`, `FiatShamir`.
- **Asymptotic definitions**: `SecurityGame` with `advantage : Adv → ℕ → ℝ`, `Negligible`,
  `Noticeable`, `SecurityReduction`.

**VCV-io already linked** in PR #404 comments by a contributor.

### PRs #401 vs #372: Competing Query Complexity Models

Two incompatible proposals:

- **PR #372 (Shreyas)**: `Model Q Cost` bundling `evalQuery` + `cost`, with `Prog.time` lifting
  through `TimeM`. Uses multi-dimensional cost (`SortOpsCost` with separate `compares`/`inserts`).
- **PR #401 (kim-em)**: Separate `Prog.eval oracle` + `Prog.queriesOn oracle` API without `Model`.

Both define `abbrev Prog Q α := FreeM Q α` (isomorphic to VCV-io's `OracleComp`).

### CSLib's Free Monad vs VCV-io's

CSLib's `FreeM F α` (freer monad, `F : Type → Type`) and VCV-io's `PFunctor.FreeM P α`
are structurally isomorphic:
- CSLib: `pure`/`liftBind`
- VCV-io: `pure`/`roll`
- Potential migration: `VCV-io OracleComp spec α ≅ CSLib FreeM (OracleQuery spec) α`

CSLib has better universal-property infrastructure (`Interprets`, `foldFreeM_unique`).
VCV-io's `simulateQ` is the analogous interpreter but lacks standalone universality theorems.

### CSLib's TimeM

```lean
structure TimeM (T : Type) (α : Type) where
  ret : α
  time : T
```

- Deterministic cost tracking as a product type
- Generalized to `[AddMonoid T]` (PR #357, merged)
- Clean projection reasoning: `time_bind`, `ret_bind` simp lemmas
- NOT probabilistic — cannot express expected cost or cost distributions

### Additive vs Multiplicative Monoid Mismatch

- **CSLib**: `TimeM` and `AddWriterT` (PR #360) use `[AddMonoid T]` for cost
- **VCV-io**: `WriterT` uses `[Monoid ω]` (multiplicative convention from Mathlib)
- Since costs compose **additively**, VCV-io should align with CSLib's additive convention

### CSLib Has No Hoare Logic

`HoareLogic` is listed in `ORGANISATION.md` as planned but has no files.
VCV-io's program logic (`Triple`, `RelTriple`, `eRelTriple`) could potentially be
contributed to CSLib's `Logics/` module.

### Compatibility Assessment

| VCV-io Component | CSLib Equivalent | Compatible? |
|-----------------|-----------------|-------------|
| `OracleComp` (free monad) | `FreeM` | Isomorphic, could migrate |
| `simulateQ` | `foldFreeM` / `Interprets` | Same concept, different API |
| `evalDist` / `PMF` | None (deterministic only) | VCV-io extends CSLib |
| `WriterT ω m` (cost) | `TimeM T` / `AddWriterT` | Subsumes, additive mismatch |
| `wp` / `Triple` / Hoare logic | Planned, not built | VCV-io leads |
| `SecExp` / `BoundedAdversary` | `SecurityGame` (PR #404) | Different paradigms |
| `Negligible` | `Negligible` (PR #404) | Harmonizable |
| `IsQueryBound` | `Prog.queriesOn` (PR #401) | Same concept |
| `costOracle` | `Model.cost` (PR #372) | Same concept |

### Compatibility Recommendations

1. **Engage SamuelSchlesinger on PR #404 now** — design is still draft. Negotiate:
   VCV-io as the probabilistic oracle-computation layer, CSLib for deterministic infrastructure.

2. **Harmonize `Negligible`** — both VCV-io and CSLib define negligible functions.
   Coordinate on a single canonical definition (ideally upstream to Mathlib).

3. **Switch to additive monoids for cost** — VCV-io's `WriterT [Monoid ω]` should migrate
   to `[AddMonoid ω]` to align with CSLib's convention. Costs compose additively.

4. **Track free monad convergence** — if CSLib's `FreeM` goes to Mathlib, consider
   redefining `OracleComp` on top of it to inherit universal-property lemmas.

5. **Offer VCV-io's program logic to CSLib** — CSLib plans `Logics/HoareLogic` but has
   nothing. VCV-io's quantitative/relational/approximate program logics could be contributed.

---

---

## Detailed Model Comparison

### A. CSLib: `TimeM` + Query Complexity

#### `TimeM T α` — Deterministic Cost Tracking

**Definition** (`Cslib/Algorithms/Lean/TimeM.lean`):
```lean
@[ext] structure TimeM (T : Type*) (α : Type*) where
  ret : α
  time : T
```

**Key operations:**
```lean
protected def pure [Zero T] (a : α) : TimeM T α := ⟨a, 0⟩
protected def bind [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret; ⟨r.ret, m.time + r.time⟩
def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩
```

**Lawfulness:** `LawfulMonad (TimeM T)` when `[AddMonoid T]`.

**Cost composition:**
- `time_bind`: `(m >>= f).time = m.time + (f m.ret).time`
- `time_pure`: `(pure a).time = 0`
- `time_map`: `(f <$> x).time = x.time` (map is free)

**Usage pattern (MergeSort):**
```lean
def merge : List α → List α → TimeM ℕ (List α)
  | x::xs', y::ys' => do
    ✓ let c := (x ≤ y : Bool)   -- ✓ = tick 1; <next>
    if c then ...
```

**Proven results:**
- `merge_time`: `(merge xs ys).time ≤ xs.length + ys.length`
- `mergeSort_time`: `(mergeSort xs).time ≤ n * ⌈log₂ n⌉`
- Full correctness: sorted + permutation

**Strengths:** Extremely clean. `.ret` and `.time` projections with `@[simp]` make proofs
short. Correctness and complexity are proven simultaneously.

**Limitations:** Purely deterministic. No probabilistic cost, no expected runtime, no tail
bounds. Cannot express "expected O(n) quickselect."

#### `Prog Q α` — Query Complexity (PR #401, kim-em)

**Core types:**
```lean
abbrev Prog (Q : Type → Type) (α : Type) := FreeM Q α

def eval (oracle : {ι : Type} → Q ι → ι) : Prog Q α → α
def queriesOn (oracle : {ι : Type} → Q ι → ι) : Prog Q α → Nat
def cost (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → Nat) : Prog Q α → Nat
```

**Bounds:**
```lean
def UpperBound (prog : α → Prog Q β) (size : α → Nat) (bound : Nat → Nat) : Prop :=
  ∀ oracle n x, size x ≤ n → (prog x).queriesOn oracle ≤ bound n

def LowerBound (prog : α → Prog Q β) (size : α → Nat) (bound : Nat → Nat) : Prop :=
  ∀ n, ∃ x, size x ≤ n ∧ ∃ oracle, bound n ≤ (prog x).queriesOn oracle
```

**Lower bound infrastructure:**
```lean
inductive QueryTree (Q R : Type) (α : Type) where
  | pure (a : α) | query (q : Q) (cont : R → QueryTree Q R α)

theorem exists_queriesOn_ge_clog [Fintype R]
    (t : QueryTree Q R α) (oracles : Fin n → (Q → R))
    (h_inj : Function.Injective (fun i => t.eval (oracles i))) :
    ∃ i, t.queriesOn (oracles i) ≥ Nat.clog (Fintype.card R) n
```

**Proven results:**
- `insertionSort_upperBound`: `UpperBound insertionSort List.length (· ^ 2)`
- `mergeSort_upperBound`: `UpperBound mergeSort List.length (fun n => n * clog 2 n)`
- `IsSort.lowerBound_infinite`: `LowerBound sort List.length (fun n => clog 2 (n!))`
- Weighted cost (Gauss mul vs naive mul): exact step counts with `ArithQuery.weight`

#### `Prog Q α` — Query Model (PR #372, Shreyas)

**Core types:**
```lean
structure Model (QType : Type u → Type v) (Cost : Type w) where
  evalQuery : QType ι → ι
  cost : QType ι → Cost

def Prog.time [AddZero Cost] (P : Prog Q α) (M : Model Q Cost) : Cost :=
  (P.liftM M.timeQuery).time     -- lifts to TimeM, reads .time

structure Reduction (Q₁ Q₂ : Type u → Type u) where
  reduce : Q₁ α → Prog Q₂ α
```

**Multi-dimensional cost:**
```lean
structure SortOpsCost where
  compares : ℕ
  inserts : ℕ
```

**Proven results:**
- `insertionSort_complexity`: multi-dimensional `(compares, inserts)` bound
- `mergeSort_complexity`: `(mergeSort xs).time (sortModelNat le) ≤ n * clog 2 n`
- `listLinearSearch` upper and lower bounds
- `cmpSort_lower_bound`: `worstTime P ≥ (n/2) * log₂(n/2)` for any correct sort

---

### B. Polytime-Formalizations (Ian Martin) — CALF-Style `MonadStep`

**Core typeclasses** (`Basic.lean`):
```lean
class MonadStep (C : outParam (Type w)) (m : Type u → Type v) where
  step : C → m PUnit

class LawfulMonadStep (C : outParam (Type w)) (m : Type u → Type v)
    [AddMonoid C] [Preorder C] [Monad m] [MonadStep C m] where
  step_zero : step (0 : C) = (pure PUnit.unit : m PUnit)
  step_add {c c' : C} : (step c >>= fun _ => step c') = (step (c' + c) : m PUnit)
```

**Cost predicates:**
```lean
def HasCost (e : m α) (cost : C) [AddMonoid C] [Monad m] [MonadStep C m] : Prop :=
  (e >>= fun _ => pure PUnit.unit : m PUnit) = step cost

def IsBounded (e : m α) (cost : C) [LE C] [AddMonoid C] [Monad m] [MonadStep C m] : Prop :=
  ∃ cost', cost' ≤ cost ∧ (HasCost e cost')
```

**Interaction with effects:**
```lean
class MonadProbStep (C m) [MonadStep C m] extends MonadProb m where
  flip_step {c} {p} {e0 e1 : m α} :
    (do step c; flip p e0 e1) = flip p (do step c; e0) (do step c; e1)

class LawfulMonadOracleStep (C P m) [MonadOracle P m] [MonadStep C m] where
  query_step {c} {a} :
    (do step c; query a : m (P.B a)) = (do let x ← query a; step c; return x)
```

**VCVio bridge** (`ProcedureCall.lean`):
```lean
instance {spec : OracleSpec ι} : MonadStep Nat (OracleComp spec) where
  step n := liftComp (step n : OracleComp []ₒ Unit) spec

lemma orchestrator_cost
    (procA procB procC) (a b c : Nat)
    (ha : IsBounded procA a) (hb : IsBounded procB b) (hc : IsBounded procC c) :
    IsBounded (handleProcC (handleProcB procA procB) procC)
      (a + b * individualQueryBound procA 0 +
       c * (individualQueryBound procA 1 + individualQueryBound procB 0)) := sorry
```

**Proven results:**
- `idHardBound`: `idHard n = step n >>= fun _ => pure n`
- `factBound`: `∃ z, fact n = step n >>= fun _ => pure z`
- `inSortCost`: `IsBounded (inSort cmp L) (L.length * L.length)`
- `insertCost`: `IsBounded (cmpInsert cmp x L) L.length`

**Strengths:** Typeclass-based, monad-generic. The `MonadProbStep`/`MonadOracleStep` classes
show how cost interacts with randomness and oracles — exactly what VCV-io needs. Already
imports VCVio.

**Limitations:** Many `sorry`s (merge sort, orchestrator_cost). CBPV axiomatization
(`Calf/CBPV.Lean`, `Calf/Step.Lean`) is broken (duplicate `axiom Cost : Type`). The
`MonadStep` instance for `OracleComp` lifts from `[]ₒ` which is awkward.

---

### C. EasyCrypt — `ehoare` + `Counter` + `OracleBounds`

#### Query Counting: `Counter` Module

```easycrypt
module Counter = {
  var c : int
  proc init(): unit = { c <- 0; }
  proc incr(): unit = { c <- c + 1; }
}.

module Count (O:Oracle) = {
  proc f(x:from): to = {
    Counter.incr();
    r <@ O.f(x);
    return r;
  }
}.
```

Memory restriction `{-Count}` prevents adversary from reading/resetting `c`.

#### Three-Way Equivalence (`OracleBounds.ec`)

1. **Enforcement** (`Enforce`): Oracle silently returns `default` after `bound` queries.
   ```easycrypt
   module Enforce(O:Oracle) = {
     proc f(x:from): to = {
       var r:to <- default;
       if (Counter.c < bound)
         r <@ O.f(x);
       return r;
     }
   }.
   ```

2. **Penalty** (`EnfPen`): `Pr[res ∧ c ≤ bound | Count(O)] ≤ Pr[res | Enforce(Count(O))]`

3. **Bounded** (`PenBnd`): `phoare[A(Count(O)).distinguish : c=0 ==> c ≤ bound] = 1`

Proven equivalences:
- `enf_implies_pen`: enforcement ⟹ penalty
- `pen_implies_bnd`: penalty (with bounded axiom) ⟹ bounded = penalty
- `bnd_implied_pen`: bounded adversary ⟹ penalty holds for enforced version

#### Expected Hoare Logic: `ehoare`

**Judgment format:**
```easycrypt
ehoare <name> : <proc> : <pre : xreal> ==> <post : xreal>
```

Means: `E[post(state')] ≤ pre(state)` — weakest preexpectation semantics over `xreal = ℝ≥0 ∪ {∞}`.

**xreal type:**
```easycrypt
type xreal = [rp of realp | oo].
op xadd, xmul, xle ...  -- standard extended arithmetic
op (`|`) (b:bool) (x : xreal) = if b then x else oo.  -- conditional assertion
```

**Expectation operator:**
```easycrypt
op Ep (d : 'a distr) (f : 'a -> xreal) : xreal  -- E_d[f]
```

Key lemmas: `EpD` (linearity), `Ep_mu` (probability as expectation of indicator),
`Ep_dlet` (bind), `Ep_dmap`, `EpC` (constant), `EpZ` (scaling).

**Bridge to probability (`byehoare`):**
```easycrypt
lemma pr_bad &m (A<:Adv{-O}) :
    Pr[Main(A).main() @ &m : O.bad] <= eps * Q%r * (inv p).
  byehoare.  -- converts Pr[event] ≤ bound to ehoare judgment
```

**Proven results:**
- Adversary `bad` event bound: `Pr[bad] ≤ ε * Q * (1/p)`
  via ehoare on log-extension oracle with expected `1/p` queries per call.
- QuickSelect expected cost: `ehoare eh_qselect : QS.qselect : ... (4*(n-1))%xr ==> c%xr`
  (expected at most `4(n-1)` comparisons).

**Strengths:** Full integration of cost reasoning with probability. The `byehoare` bridge
is exactly the Markov inequality. Handles expected-time algorithms (quickselect) and
adversarial complexity bounds (birthday, bad events) in the same framework.

**Limitations:** Imperative (while loops, mutable state). Module-system-based adversary
abstraction (not type-based). No distributional cost reasoning beyond expectation (no
variance, no tail bounds beyond Markov).

---

### D. Summary Comparison Table

| Feature | CSLib TimeM | CSLib Prog (PR #401/#372) | Polytime-Formalizations | EasyCrypt ehoare |
|---|---|---|---|---|
| **Cost type** | `T : Type*` with `[AddMonoid T]` | `Nat` or polymorphic `Cost` | `C : Type*` with `[AddMonoid C]` | `xreal = ℝ≥0 ∪ {∞}` |
| **Cost tracking** | Product type `(ret, time)` | Structural recursion on free monad | `step c` in do-notation | Mutable variable + `ehoare` |
| **Composition** | `time_bind`: additive | `cost_bind`: additive | `step_add`: equational | Sequential `ehoare` rule |
| **Probabilistic?** | No | No | Yes (`MonadProb`, `MonadProbStep`) | Yes (`Ep`, `distr`) |
| **Expected cost?** | No | No | No (deterministic proofs only) | Yes (`Ep d f`) |
| **Tail bounds?** | No | No | No | Via `byehoare` (Markov only) |
| **Query counting** | N/A | `queriesOn`, `cost` | `individualQueryBound` | `Counter` module |
| **Lower bounds?** | No | Yes (`QueryTree`, `clog(n!)`) | No | No |
| **Oracle interaction** | None | `Prog Q α` (free monad) | `MonadOracle P m` class | Module system |
| **Adversary abstraction** | N/A | N/A | N/A | Module types + `{-Counter}` |
| **VCVio integration** | None (standalone) | Isomorphic free monad | Imports VCVio directly | N/A (OCaml) |
| **Maturity** | Merged, proven MergeSort | Draft PRs, proven results | WIP, many `sorry`s | Production, proven QuickSelect |
| **Cost model** | Trusted `tick` annotations | Structural (per query) | Trusted `step` annotations | Trusted annotations |

### E. Key Design Insights From Each Framework

**From CSLib TimeM:**
- Product type `(ret, time)` is the simplest correct approach
- `@[simp]` on `ret_*` / `time_*` projections makes automation trivial
- `✓` notation for `tick` is ergonomic

**From CSLib Prog (#401):**
- `UpperBound`/`LowerBound` as first-class definitions, universally quantified over oracles
- `QueryTree` with `exists_queriesOn_ge_clog` gives information-theoretic lower bounds
- `queriesOn_eq_cost_one`: uniform query counting is a special case of weighted cost
- Weighted cost (`ArithQuery.weight c_add c_mul`) distinguishes operation types

**From CSLib Prog (#372):**
- Bundled `Model Q Cost` is cleaner than separate oracle + cost parameters
- Multi-dimensional cost (`SortOpsCost`) with `AddCommMonoid` is natural
- `Reduction Q₁ Q₂` for relating different query types (foreshadows crypto reductions)
- `worstTime` as `Finset.sup` over all possible oracles

**From Polytime-Formalizations:**
- `MonadStep` is monad-generic — works for any `m`, including `OracleComp`
- `MonadProbStep.flip_step` shows cost distributes over probabilistic choice
- `LawfulMonadOracleStep.query_step` shows cost commutes with oracle queries
- `orchestrator_cost` captures how costs compose through `simulateQ` reductions

**From EasyCrypt ehoare:**
- `xreal = ℝ≥0 ∪ {∞}` is the right carrier (matches Lean's `ℝ≥0∞` / `ENNReal`)
- `E[post] ≤ pre` (weakest preexpectation) is the same as VCV-io's `wp`
- Conditional assertion `b \`|\` x` cleanly connects boolean events to expectations
- `byehoare` (Markov bridge) is the single most useful theorem
- `Ep_dlet` (bind rule for expectations) is critical for compositional reasoning

---

## Next Steps

1. Prototype Markov bridge lemma: `Pr[cost > t | oa] ≤ expectedCost oa cm / t`
2. Define `CostModel`, `costDist`, `expectedCost`
3. Define `SecurityExp` wrapping `SecExp`
4. Define `PolyQueries` and `PPTAdversary`
5. Wire `negligible` into `SecurityExp.secure`
6. Switch `WriterT` from `[Monoid ω]` to `[AddMonoid ω]`
7. Coordinate with ianm1129/Polytime-Formalizations
8. Engage SamuelSchlesinger on CSLib PR #404
9. Harmonize `Negligible` definition across VCV-io/CSLib/Mathlib
