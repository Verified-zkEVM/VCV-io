# Crypto Primitives and Reductions

## Crypto Primitive Structures

### Asymmetric encryption (`AsymmEncAlg`)

```lean
structure AsymmEncAlg (m : Type → Type) (M PK SK C : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  encrypt : PK → M → m C
  decrypt : SK → C → Option M
```

### Symmetric encryption (`SymmEncAlg`)

```lean
structure SymmEncAlg (M K C : ℕ → Type) (Q : Type)
    extends OracleContext Q ProbComp where
  keygen (sp : ℕ) : OracleComp spec (K sp)
  encrypt {sp : ℕ} (k : K sp) (msg : M sp) : OracleComp spec (C sp)
  decrypt {sp : ℕ} (k : K sp) (c : C sp) : OptionT (OracleComp spec) (M sp)
```

### Signatures (`SignatureAlg`)

```lean
structure SignatureAlg (m : Type → Type) (M PK SK S : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : m S
  verify (pk : PK) (msg : M) (σ : S) : m Bool
```

### Sigma protocols (`SigmaProtocol`)

```lean
structure SigmaProtocol (S W PC SC Ω P : Type) (p : S → W → Bool) where
  commit (s : S) (w : W) : ProbComp (PC × SC)
  respond (s : S) (w : W) (sc : SC) (ω : Ω) : ProbComp P
  verify (s : S) (pc : PC) (ω : Ω) (p : P) : Bool
  sim (s : S) : ProbComp PC
  extract (ω₁ : Ω) (p₁ : P) (ω₂ : Ω) (p₂ : P) : ProbComp W
```

### Key difference: `OracleContext` vs `ExecutionMethod`

- `SymmEncAlg` extends `OracleContext` — operations are `OracleComp spec`, spec comes from context
- `AsymmEncAlg` / `SignatureAlg` extend `ExecutionMethod` — operations are in abstract `m`, converted via `exec`

### Instantiation pattern

```lean
@[simps!] def myAlg : AsymmEncAlg ProbComp M PK SK C where
  keygen := do ...
  encrypt pk msg := do ...
  decrypt sk c := ...
  __ := ExecutionMethod.default
```

For `SymmEncAlg`, use `__ := unifSpec.defaultContext`.

## Security Experiments

### `SecExp`

```lean
structure SecExp (m : Type → Type) extends ExecutionMethod m where
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
structure GenerableRelation (X W : Type) (r : X → W → Bool)
    [SampleableType X] [SampleableType W] where
  gen : ProbComp (X × W)
  gen_sound (x : X) (w : W) : (x, w) ∈ support gen → r x w
  gen_uniform_right (x : X) : Pr[= x | Prod.fst <$> gen] = Pr[= x | $ᵗ X]
  gen_uniform_left (w : W) : Pr[= w | Prod.snd <$> gen] = Pr[= w | $ᵗ W]
```

Note: the relation is `r : X → W → Bool` (not `Prop`), and `[SampleableType]` instances are required for both types.

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

For q-query IND-CPA → DDH (as in `Examples/ElGamal/Basic.lean`):

1. Define `HybridGame adversary k`: first `k` queries use real encryption, rest use random
2. `HybridGame 0 = IND-CPA random`, `HybridGame q = IND-CPA real`
3. Per-step reduction: `stepDDHReduction adversary k` maps DDH challenge to hybrid k vs k+1
4. Telescope: `advantage ≤ q * max_per_step_advantage`

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

2. **`SymmEncAlg` vs `AsymmEncAlg`**: different parent classes (`OracleContext` vs `ExecutionMethod`), different oracle access patterns.

3. **DDH experiment uses `$ᵗ Bool`**: the experiment samples a bit `b`, returns real or random based on `b`, then checks `b == b'`.

4. **`SecExp.advantage` measures `1 - Pr[⊥]`**: this is failure-based, not distinguishing-based. For `ProbComp` (which never fails), advantage is always 1. For distinguishing-style games, use `SecurityGame.ofDistGame` or `SecurityGame.ofGuessGame` instead of `SecurityGame.ofSecExp`.
