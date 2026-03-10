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

### `SecAdv`

```lean
structure SecAdv {ι : Type u} [DecidableEq ι]
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
| `ProbComp.advantage` | `ProbComp Unit` | `ℝ` | `\|1/2 - (Pr[= () \| p]).toReal\|` |
| `ProbComp.advantage'` | `ProbComp Bool` | `ℝ` | `\|(Pr[= true \| p]).toReal - (Pr[= false \| p]).toReal\|` |
| `ProbComp.advantage₂` | Two `ProbComp Unit` | `ℝ` | `\|(Pr[= () \| p]).toReal - (Pr[= () \| q]).toReal\|` |
| `ProbComp.advantage₂'` | Two `ProbComp Bool` | `ℝ` | `\|(Pr[= true \| p]).toReal - (Pr[= true \| q]).toReal\|` |

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

For q-query IND-CPA → DDH (as in `Examples/ElGamal.lean`):

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

## Common Gotchas

1. **Avoid `guard`**: use `return (b == b')` or `return decide (r x w)` instead. `guard` requires `OptionT` / `Alternative`.

2. **`SymmEncAlg` vs `AsymmEncAlg`**: different parent classes (`OracleContext` vs `ExecutionMethod`), different oracle access patterns.

3. **DDH experiment uses `$ᵗ Bool`**: the experiment samples a bit `b`, returns real or random based on `b`, then checks `b == b'`.
