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
structure SecAdv (spec : OracleSpec ι) (α β : Type) where
  run : α → OracleComp spec β
  qb : ι → ℕ                    -- per-index query bound
  activeOracles : List ι
```

### Advantage functions

| Function | Input | Measures |
|----------|-------|----------|
| `ProbComp.advantage` | `ProbComp Unit` | `|1/2 - Pr[= () \| p]|` |
| `ProbComp.advantage'` | `ProbComp Bool` | `|Pr[= true \| p] - Pr[= false \| p]|` |
| `ProbComp.advantage₂` | Two `ProbComp Unit` | `|Pr[= () \| p] - Pr[= () \| q]|` |
| `ProbComp.advantage₂'` | Two `ProbComp Bool` | `|Pr[= true \| p] - Pr[= true \| q]|` |

## Hardness Assumptions

### Hard Homogeneous Spaces (HHS)

Requires `[AddCommGroup G] [AddTorsor G P] [SampleableType G] [SampleableType P]`.

| Problem | Adversary type | Experiment |
|---------|---------------|------------|
| DLog (vectorization) | `P → P → ProbComp G` | `vectorizationExp` |
| CDH (parallelization) | `P → P → P → ProbComp P` | `parallelizationExp` |
| DDH (parallel testing) | `P → P → P → P → ProbComp Bool` | `parallelTesting_experiment` |

DDH abbreviations: `ddhExp`, `ddhAdvantage` (in `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`).

### Hard Relations

```lean
structure GenerableRelation (X W : Type) (r : X → W → Bool) where
  gen : ProbComp (X × W)
  gen_sound : ∀ x w, (x, w) ∈ support gen → r x w
  gen_uniform_right : ∀ x, Pr[= x | Prod.fst <$> gen] = Pr[= x | $ᵗ X]
  gen_uniform_left : ∀ w, Pr[= w | Prod.snd <$> gen] = Pr[= w | $ᵗ W]
```

Note: the relation is `r : X → W → Bool` (not `Prop`).

## Building a Reduction

A reduction proves: if adversary A breaks scheme S, then adversary B breaks assumption H.

### Blueprint

1. **Define the reduction adversary** that takes a challenge from H and embeds it into S:

```lean
def myReduction (adversary : ...) : DDHAdversary G P := fun x x₁ x₂ x₃ => do
  -- embed (x, x₁, x₂, x₃) as scheme parameters
  let result ← adversary ...
  -- convert adversary's output to DDH guess
  return result
```

2. **Prove the probability identity**: show that the reduction's advantage equals (or bounds) the scheme adversary's advantage.

3. **Key technique**: hybrid arguments for multi-query reductions.

### Hybrid Argument Pattern

For q-query IND-CPA → DDH (as in `HHS_Elgamal.lean`):

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
