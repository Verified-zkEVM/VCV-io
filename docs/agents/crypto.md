# Crypto Primitives and Reductions

For the `LatticeCrypto/` directory layout, scheme entry points, and proof-vs-concrete split,
see [`docs/agents/lattice.md`](lattice.md).

## Crypto Primitive Structures

### Asymmetric encryption (`AsymmEncAlg`)

```lean
structure AsymmEncAlg (m : Type → Type u) [Monad m] (M PK SK C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → m C
  decrypt : (sk : SK) → (c : C) → m (Option M)
```

### Symmetric encryption (`SymmEncAlg`)

```lean
structure SymmEncAlg (m : Type → Type u) [Monad m] (M K C : Type) where
  keygen : m K
  encrypt : K → M → m C
  decrypt : K → C → m (Option M)
```

### Signatures (`SignatureAlg`)

```lean
structure SignatureAlg (m : Type → Type v) [Monad m] (M PK SK S : Type) where
  keygen : m (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : m S
  verify (pk : PK) (msg : M) (σ : S) : m Bool
```

For an end-to-end EUF-CMA reduction worked through the framework (Σ-protocol →
Fiat-Shamir transform → managed-RO NMA → replay forking → DLog), see
[`Examples/Schnorr/Signature.lean`](../../Examples/Schnorr/Signature.lean) and the
[Schnorr signature walkthrough](end-to-end-examples.md#schnorr-signature-euf-cma).
The Schnorr-specific σ-protocol facts that feed in live in
[`Examples/Schnorr/SigmaProtocol.lean`](../../Examples/Schnorr/SigmaProtocol.lean).

### Commitment schemes (`CommitmentScheme`)

```lean
structure CommitmentScheme (PP M C D : Type) where
  setup : ProbComp PP
  commit (pp : PP) (m : M) : ProbComp (C × D)
  verify (pp : PP) (m : M) (c : C) (d : D) : Bool
```

Defined in
[`VCVio/CryptoFoundations/CommitmentScheme.lean`](../../VCVio/CryptoFoundations/CommitmentScheme.lean)
together with `PerfectlyCorrect`, `PerfectlyHiding`, `hidingExp`,
`bindingExp`, and `extractExp`. The standard-model `binding ≤ keyed-CR ≤
birthday` bridge from a `KeyedHashFamily` lives in
[`VCVio/CryptoFoundations/HashCommitment.lean`](../../VCVio/CryptoFoundations/HashCommitment.lean)
as `bindingAdvantage_toCommitment_le_keyedCRAdvantage`.

For an end-to-end ROM proof of binding, extractability, and hiding for the
textbook `Commit(m) = (H(m, s), s)` scheme — exercising `cachingOracle`,
`loggingOracle`, the birthday bound, and identical-until-bad — see
[`Examples/CommitmentScheme.lean`](../../Examples/CommitmentScheme.lean)
and the
[ROM commitment scheme walkthrough](end-to-end-examples.md#rom-commitment-scheme).

### Challenge-verify protocols and sigma protocols (`ChallengeVerifyProtocol`, `SigmaProtocol`)

```lean
structure ChallengeVerifyProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool)
    (m : Type → Type) where
  commit (stmt : Stmt) (wit : Wit) : m (Commit × PrvState)
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) : m Resp
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool

structure SigmaProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool)
    (m : Type → Type)
    extends ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel m where
  sim (stmt : Stmt) : m Commit
  extract (chal₁ : Chal) (resp₁ : Resp) (chal₂ : Chal) (resp₂ : Resp) : m Wit
```

`ChallengeVerifyProtocol` is the bare commit-challenge-response interaction; take it when the
extractor is irrelevant. `SigmaProtocol` adds the simulator and extractor as data, so consumers
such as the Fischlin transform and the Fiat-Shamir Σ-layer can run them. Dot notation resolves
through the parent projection, so a `SigmaProtocol` uses the interaction properties directly.

The monad `m` carries the participants' computations: `m := ProbComp` is the usual protocol whose
only randomness is uniform sampling, while a general `m` lets the prover query oracles.
Probability-bearing properties (`PerfectlyComplete`, `HVZK`, `PerfectHVZK`,
`simCommitPredictability`, `simChalUniformGivenCommit`) are measure-native: they assume
`[EvalDistSemantics m]` and read the protocol through `discreteEvalDist` / `discreteTVDist`
(the canonical top-σ-algebra measure reading, since the protocol's type parameters carry no
ambient measurable structure). Support-bearing notions (`SpeciallySound`) assume only
`[MonadLiftT m SetM]`. At `m := ProbComp` every property is restated through the traditional
`Pr[…]` / `tvDist` surface by a companion bridge lemma (`perfectlyComplete_iff_probOutput`,
`hvzk_iff_tvDist`, `perfectHVZK_iff_evalSPMF_eq`, `simCommitPredictability_iff_probOutput`,
`simChalUniformGivenCommit_iff_probEvent`) with application-shaped forms such as
`PerfectlyComplete.probOutput_eq_one` and `HVZK.tvDist_le`; the discrete developments prove and
consume the definitions exclusively through these bridges
(`VCVio/EvalDist/DiscreteMeasureCompat.lean` supplies the underlying dictionary). Caveat for
oracle-querying provers: the probability denotation of `OracleComp spec` samples a fresh
independent response per query, so a shared random oracle (equal inputs must get equal answers)
must be interpreted through the caching layer (`OracleSpec.cachingOracle` / `withCacheOverlay`)
before taking its probability denotation. `PerfectlyComplete` quantifies over the verifier's
challenge pointwise, so it needs no sampling structure on `m`; at `m := ProbComp` it is
equivalent to the sampled form (`perfectlyComplete_iff_probOutput_uniform_challenge_eq_one`,
directions `PerfectlyComplete.probOutput_uniform_challenge_eq_one` and
`perfectlyComplete_of_probOutput_uniform_challenge_eq_one`). The transcript-facing properties
(`realTranscript`, `HVZK`, `PerfectHVZK`) draw the challenge as `liftM ($ᵗ Chal)` and so ask for
`[SampleableType Chal] [MonadLiftT ProbComp m]`; at `m := ProbComp` that is definitionally the
plain `$ᵗ Chal` (`realTranscript_probComp`).
`PerfectlyComplete`, `HVZK`, `UniqueResponses`, and `realTranscript` live on
`ChallengeVerifyProtocol`; `SpeciallySound` lives on `SigmaProtocol`, since it consumes `extract`.

Every `ProbComp`-valued `ChallengeVerifyProtocol` coerces to `IdenSchemeWithAbort` via
`toIdenSchemeWithAbort` (wraps `respond` with `some`).

### Identification scheme with aborts (`IdenSchemeWithAbort`)

```lean
structure IdenSchemeWithAbort
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) :
    ProbComp (Option Resp)
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool
```

The key difference from `SigmaProtocol` is that `respond` returns `Option Resp` (abort on `none`).
Used by ML-DSA and the Fiat-Shamir with Aborts transform.

### Key difference: monad-parametric algorithm surfaces

- `SymmEncAlg`, `AsymmEncAlg`, and `SignatureAlg` are plain structures over an abstract monad `m`.
- Instantiate them with `ProbComp`, `OracleComp spec`, `OptionT (OracleComp spec)`, or another monad at the security surface that needs those effects.
- Probability and failure semantics are supplied by the surrounding experiment or semantic class, not by parent classes on the algorithm structure.

### Instantiation pattern

```lean
@[simps!] def myAlg : AsymmEncAlg ProbComp M PK SK C where
  keygen := do ...
  encrypt pk msg := do ...
  decrypt sk c := do ...
```

## Security Experiments

### `SecExp`

```lean
structure SecExp (m : Type → Type w) [Monad m] extends SPMFSemantics m where
  main : m Unit
```

Success = non-failure. Advantage: `1 - Pr[⊥ | exp.main]`.

### `BoundedAdversary`

```lean
structure BoundedAdversary {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0
```

### Advantage functions

| Function | Input | Type | Measures |
|----------|-------|------|----------|
| `ProbComp.guessAdvantage` | `ProbComp Unit` | `ℝ` | `\|1/2 - (Pr[= () \| p]).toReal\|` |
| `ProbComp.boolBiasAdvantage` | `ProbComp Bool` | `ℝ` | `\|(Pr[= true \| p]).toReal - (Pr[= false \| p]).toReal\|` |
| `ProbComp.distAdvantage` | Two `ProbComp Unit` | `ℝ` | `\|(Pr[= () \| p]).toReal - (Pr[= () \| q]).toReal\|` |
| `ProbComp.boolDistAdvantage` | Two `ProbComp Bool` | `ℝ` | `\|(Pr[= true \| p]).toReal - (Pr[= true \| q]).toReal\|` |

All return `ℝ` via `.toReal` conversion from `ℝ≥0∞`. This is essential since subtraction on `ℝ≥0∞` is truncated.

### Forking bounds and measure semantics

`VCVio/CryptoFoundations/SeededFork.lean` and `ReplayFork.lean` prove the
seeded and context-fork success bounds through the established `Pr[...]`
surface. `ForkMeasure.lean` states the same final bounds as the Mathlib measure
of the `Option.isSome` event, using the canonical measure semantics induced by
the oracle specification's existing per-query probability interpretation.
These are transport corollaries; the forking arguments remain in the two
original modules.

## Hardness Assumptions

### Discrete Log Assumptions (DLog / CDH / DDH)

Requires `[Field F] [Fintype F] [DecidableEq F] [SampleableType F]` and
`[AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]`
plus a fixed generator `g : G`.

Uses additive / EC-style notation: `a • g` means scalar multiplication (textbook `g^a`).

| Problem | Adversary type | Experiment |
|---------|---------------|------------|
| DLog | `DLogAdversary F G` (= `G → G → ProbComp F`) | `dlogExp g adversary` |
| CDH | `CDHAdversary F G` (= `G → G → G → ProbComp G`) | `cdhExp g adversary` |
| DDH | `DDHAdversary F G` (= `G → G → G → G → ProbComp Bool`) | `ddhExp g adversary` |

`CDHAdversary` and `DDHAdversary` carry a phantom `_F` parameter so Lean can infer the scalar field at call sites.

Defined in `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`.

### Hard Relations

```lean
structure GenerableRelation (X W : Type) (r : X → W → Bool) where
  gen : ProbComp (X × W)
  gen_sound (x : X) (w : W) : (x, w) ∈ support gen → r x w
```

Note: the relation is `r : X → W → Bool` (not `Prop`). If a reduction needs
uniform marginal guarantees, state them as separate hypotheses or structure fields.

## Building a Reduction

A reduction proves: if adversary A breaks scheme S, then adversary B breaks assumption H.

### Blueprint

1. **Define the reduction adversary** that takes a challenge from H and embeds it into S:

```lean
def myReduction (adversary : ...) : DDHAdversary F G := fun g A B T => do
  -- embed DDH challenge (g, A = a•g, B = b•g, T) as scheme parameters
  let result ← adversary ...
  return result
```

2. **Prove the probability identity**: show that the reduction's advantage equals (or bounds) the scheme adversary's advantage.

3. **Key technique**: hybrid arguments for multi-query reductions.

### Hybrid Argument Pattern

For a hand-written q-query IND-CPA → DDH hybrid proof:

1. Define `HybridGame adversary k`: first `k` queries use real encryption, rest use random
2. `HybridGame 0 = IND-CPA random`, `HybridGame q = IND-CPA real`
3. Per-step reduction: `stepDDHReduction adversary k` maps DDH challenge to hybrid k vs k+1
4. Telescope: `advantage ≤ q * max_per_step_advantage`

`Examples/ElGamal/Basic.lean` currently obtains its q-query bound by instantiating
the generic one-time IND-CPA lift in `VCVio/CryptoFoundations/AsymmEncAlg/INDCPA/GenericLift.lean`.

### Oracle Wiring for Stateful Reductions

Use `StateT` for reductions that need to track state (e.g., query counter, cache):

```lean
def myQueryImpl (challenge : ...) :
    QueryImpl spec (StateT MyState ProbComp) := fun t => do
  let st ← get
  -- branch on state to embed challenge
  ...
```

## Asymptotic Security

Defined in `VCVio/CryptoFoundations/Asymptotics/`.

### Negligible functions (`Negligible.lean`)

```lean
def negligible (f : ℕ → ℝ≥0∞) : Prop := SuperpolynomialDecay atTop (fun x ↦ ↑x) f
```

Closure properties: `negligible_add`, `negligible_const_mul`, `negligible_sum`,
`negligible_of_le`, `negligible_pow_mul`, `negligible_polynomial_mul`.

### `SecurityExp` and `SecurityGame` (`Security.lean`)

Both are decoupled from `SecExp` — they store an abstract advantage function (`ℕ → ℝ≥0∞`)
rather than a family of concrete experiments. This lets the same meta-theorems work for
failure-based games, distinguishing games, and any other advantage metric.

```lean
structure SecurityExp where
  advantage : ℕ → ℝ≥0∞

structure SecurityGame (Adv : Type*) where
  advantage : Adv → ℕ → ℝ≥0∞
```

- `SecurityExp.secure`: advantage is `negligible`.
- `SecurityGame.secureAgainst isPPT`: every adversary satisfying `isPPT` has negligible advantage.
- The predicate `isPPT` is abstract — specialize to `PolyQueries` or custom efficiency notions.

### Smart constructors

| Constructor | Game style | Advantage metric |
|-------------|-----------|-----------------|
| `SecurityGame.ofSecExp` | Failure-based (`SecExp`) | `1 - Pr[⊥]` |
| `SecurityGame.ofDistGame` | Two-game distinguishing | `\|Pr[game₀] - Pr[game₁]\|` |
| `SecurityGame.ofGuessGame` | Single-game guessing | `\|1/2 - Pr[success]\|` |

Analogous constructors exist for `SecurityExp`: `ofSecExp`, `ofDistExp`, `ofGuessExp`.

### Key reduction/game-hopping lemmas

| Lemma | Use |
|-------|-----|
| `secureAgainst_of_reduction` | Tight reduction: `adv(A) ≤ adv(reduce A)` |
| `secureAgainst_of_poly_reduction` | Polynomial-loss: `adv(A) ≤ p(n) · adv(reduce A)` |
| `secureAgainst_of_close` | Game hop: `adv_g₁(A) ≤ adv_g₂(A) + ε(n)` |
| `secureAgainst_of_hybrid` | Chain of `k` games differing by `ε` each |

## Cost Model

Defined in `VCVio/OracleComp/QueryTracking/CostModel.lean`. Uses `AddWriterT ω` for
additive cost accumulation through `simulateQ`.

```lean
structure CostModel (spec : OracleSpec ι) (ω : Type) [AddCommMonoid ω] where
  queryCost : spec.Domain → ω
```

| Definition | Purpose |
|------------|---------|
| `costDist oa cm` | Joint distribution `(output, totalCost)` |
| `expectedCost oa cm val` | `E[val(cost)]` via `wp` |
| `WorstCaseCostBound oa cm bound` | All paths have cost `≤ bound` |
| `ExpectedCostBound oa cm val bound` | Expected valued cost `≤ bound` |
| `WorstCasePolyTime family cm val` | Worst-case poly bound over security parameter |
| `ExpectedPolyTime family cm val` | Expected poly bound over security parameter |

Key results: `fst_map_costDist` (instrumentation is transparent),
`probEvent_cost_gt_le_expectedCost_div` (Markov's inequality),
`WorstCasePolyTime.toExpectedPolyTime`.

## Common Gotchas

1. **Avoid `guard`**: use `return (b == b')` or `return decide (r x w)` instead. `guard` requires `OptionT` / `Alternative`.

2. **`SymmEncAlg` vs `AsymmEncAlg`**: both are monad-parametric, but symmetric schemes carry a single key type while asymmetric schemes split public and secret keys. Pick the monad at the experiment boundary.

3. **DDH experiment uses `$ᵗ Bool`**: the experiment samples a bit `b`, returns real or random based on `b`, then checks `b == b'`.

4. **`SecExp.advantage` measures `1 - Pr[⊥]`**: this is failure-based, not distinguishing-based. For `ProbComp` (which never fails), advantage is always 1. For distinguishing-style games, use `SecurityGame.ofDistGame` or `SecurityGame.ofGuessGame` instead of `SecurityGame.ofSecExp`.
