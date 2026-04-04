# Reduction Cost Accounting Design

This note sketches a VCV-io design for **explicit cost accounting of reductions**.
The target use case is a theorem of the form:

```text
for every adversary A against game G,
there is a reduced adversary B against game H such that

  advantage_G(A) ≤ advantage_H(B) + ε
  cost(B) ≤ transform(cost(A)).
```

The design is inspired by the EasyCrypt paper
[`Mechanized_Proofs_of_Adversarial_Complexity_2021_156.pdf`](/Users/quang.dao/Documents/Papers/Mechanized_Proofs_of_Adversarial_Complexity_2021_156.pdf),
but adapted to the semantic architecture that already exists in VCV-io:

- `AddWriterT` for cost instrumentation,
- `QueryRuntime` for open query semantics,
- `SecurityGame` for quantified reduction theorems.

## Design Goals

We want a cost model that is:

1. **Compositional for open code**.
   A reduction body should be analyzable before we instantiate the adversary it calls.
2. **Compatible with the current weighted query-cost framework**.
   Structured cost should refine, not replace, the scalar `QueryCost` story.
3. **Strong enough for reduction composition lemmas**.
   If one reduction absorbs another, cost transforms should compose automatically.
4. **Honest about cryptographic practice**.
   We should distinguish:
   - the reduction's own intrinsic runtime;
   - the number of times it invokes external capabilities.

## Core Observation

The EasyCrypt paper models the cost of open code as:

- an **intrinsic** cost component;
- plus one coordinate per **abstract call**.

In VCV-io, we should make the same split, but with a single notion of
external interface usage. We should **not** distinguish "query" and "call" in
the core object. In our setting, both are just interactions with an open interface.

## Proposed Core Object

The most natural core type is:

```lean
structure ResourceProfile (ω : Type*) (κ : Type*) where
  intrinsic : ω
  usage : κ →₀ ℕ
```

Interpretation:

- `ω` is the type of intrinsic runtime cost.
- `κ` indexes the external capabilities exposed by the open interface.
- `usage k` is how many times the open program invokes capability `k`.

This is the key departure from a purely scalar weighted cost:

- `intrinsic` is already a concrete cost in `ω`;
- `usage` is still symbolic.

The symbolic part is what makes composition possible.

## Why `intrinsic : ω` Instead Of Ticks?

Intrinsic runtime should not be forced into unit ticks.

If we want:

- ordinary natural-number runtime, take `ω := ℕ`;
- asymptotic polynomials, take `ω := Polynomial ℕ` or a suitable bound type;
- multi-coordinate intrinsic cost later, take `ω` itself to be a profile type.

So the right first design is:

- concrete intrinsic cost in `ω`;
- symbolic external usage in `κ →₀ ℕ`.

## What Should `κ` Be?

`κ` should index **capabilities**, not raw oracle arguments.

Examples:

- for a two-phase IND-CPA adversary:
  `κ := { chooseMessages, distinguish }`
- for a UC-style environment:
  `κ := { inputs, outputs, backdoor, step }`
- for an oracle-backed reduction:
  `κ` can be the family/operation names of the oracles it uses

In many concrete reductions, the open interface will still be implemented as an oracle,
but the cost theorem should usually speak at the level of interface operations,
not full query domains.

## Candidate Names

Possible names for the core structure:

1. `ResourceProfile`
   - Best semantic fit.
   - Reads naturally in reduction theorems.
   - Recommended default.

2. `CostProfile`
   - Short and conventional.
   - Slightly less explicit about the symbolic/interface aspect.

3. `OpenCost`
   - Emphasizes "cost of open code".
   - Short, but a bit too vague once instantiated.

4. `CapabilityCost`
   - Makes the interface-indexed nature explicit.
   - A bit clunky for theorem statements.

5. `InteractionProfile`
   - Good if we want to emphasize the external-usage side.
   - Weaker on the intrinsic-runtime side.

Current recommendation:

- use `ResourceProfile` for the structure;
- reserve `OpenCost` for prose if we want a generic phrase.

## Algebra On Resource Profiles

We need two fundamental operations.

### Scalar Evaluation

Given per-capability costs `w : κ → ω`, we can evaluate a resource profile to a scalar cost:

```lean
def ResourceProfile.eval
    [CanonicallyOrderedAddMonoid ω]
    (c : ResourceProfile ω κ) (w : κ → ω) : ω :=
  c.intrinsic + c.usage.sum (fun k n => n • w k)
```

This is the bridge back to the existing weighted-cost framework.

### Instantiation / Substitution

If an external capability `k` is itself implemented by open code with profile `impl k`,
we can substitute it into the outer profile:

```lean
def ResourceProfile.instantiate
    [CanonicallyOrderedAddMonoid ω]
    (c : ResourceProfile ω κ)
    (impl : κ → ResourceProfile ω κ') :
    ResourceProfile ω κ'
```

Intuitively:

- keep `c.intrinsic`,
- for each `k` used `n` times, add `n` copies of `impl k`.

This is the VCV-io analogue of the EasyCrypt paper's transformed cost bounds `ĉ`.

## Core Composition Lemmas

These are the real north-star algebraic theorems.

```lean
theorem ResourceProfile.instantiate_assoc
    [CanonicallyOrderedAddMonoid ω]
    (c : ResourceProfile ω κ)
    (impl₁ : κ → ResourceProfile ω κ')
    (impl₂ : κ' → ResourceProfile ω κ'') :
    (c.instantiate impl₁).instantiate impl₂ =
      c.instantiate (fun k => (impl₁ k).instantiate impl₂)
```

```lean
theorem ResourceProfile.eval_instantiate
    [CanonicallyOrderedAddMonoid ω]
    (c : ResourceProfile ω κ)
    (impl : κ → ResourceProfile ω κ')
    (w : κ' → ω) :
    (c.instantiate impl).eval w =
      c.eval (fun k => (impl k).eval w)
```

These two lemmas explain why reduction-cost transforms compose.

## Where This Sits In The Existing Stack

This should be a richer cost type for the writer-based framework, not a new semantics.

The intended implementation route is:

1. Instantiate `AddWriterT` with `ResourceProfile ω κ`.
2. Use `QueryRuntime.withAddCost` / related machinery to account for open interface usage.
3. Prove structured pathwise and expected-cost theorems using the current framework.
4. Recover scalar weighted statements via `ResourceProfile.eval`.

So the structured layer refines the current `QueryCost` / `ExpectedQueryCost` layer.

## Open Reductions

For reduction cost accounting, we should reason first about an **open reduction body**.

Example: the one-time ElGamal DDH reduction currently consumes an adversary structure
with procedures `chooseMessages` and `distinguish`.

For cost analysis, we should reify that interface as a capability type:

```lean
inductive INDCPAOneTimeCap
| chooseMessages
| distinguish
```

Then define an open reduction body whose external calls target this interface.
The first cost theorem should be about that open body.

## ElGamal Example: North-Star Theorem

[Examples/ElGamal/Basic.lean](/Users/quang.dao/Documents/Lean/VCV-io/Examples/ElGamal/Basic.lean)
is a good initial target because the reduction is explicit and simple.

The open-body theorem we want is roughly:

```lean
theorem IND_CPA_OneTime_DDHReduction_open_cost
    (gen : G) :
    UsesResourceAtMost
      (IND_CPA_OneTime_DDHReduction_open (F := F) (G := G) gen)
      { intrinsic := c₀,
        usage := Finsupp.single .chooseMessages 1
               + Finsupp.single .distinguish 1 } := ...
```

Mathematically:

- the reduction itself pays intrinsic cost `c₀`;
- it calls `chooseMessages` once;
- it calls `distinguish` once.

After instantiating those capabilities with a concrete adversary profile, we should get:

```lean
theorem IND_CPA_OneTime_DDHReduction_cost
    (A : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen))
    (hA : adversaryProfile A ≤ cA) :
    reductionProfile (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) A)
      ≤ openProfile.instantiate cA := ...
```

At the scalar level, this specializes to:

```text
cost(B) ≤ intrinsic_overhead + cost_chooseMessages(A) + cost_distinguish(A).
```

## Reduction Packaging

At the adversary/game layer, we want a bundled notion of reduction with cost transform.

One plausible north-star structure is:

```lean
structure ReductionWithCost
    (Adv Adv' : Type*)
    (ω : Type*) (κ κ' : Type*) where
  reduce : Adv → Adv'
  transform : ℕ → ResourceProfile ω κ → ResourceProfile ω κ'
  monotone' : ∀ n, Monotone (transform n)
  cost_bound :
    ∀ A n, costProfile (reduce A) n ≤ transform n (costProfile A n)
```

Then the key composition theorem is:

```lean
def ReductionWithCost.comp
    (R₁ : ReductionWithCost Adv₁ Adv₂ ω κ₁ κ₂)
    (R₂ : ReductionWithCost Adv₂ Adv₃ ω κ₂ κ₃) :
    ReductionWithCost Adv₁ Adv₃ ω κ₁ κ₃ where
  reduce := R₂.reduce ∘ R₁.reduce
  transform n := R₂.transform n ∘ R₁.transform n
  ...
```

This is the reduction-level analogue of `ResourceProfile.instantiate_assoc`.

## Security-Level North Star

The existing asymptotic reduction theorem in
[Security.lean](/Users/quang.dao/Documents/Lean/VCV-io/VCVio/CryptoFoundations/Asymptotics/Security.lean)
should eventually gain a cost-aware analogue:

```lean
theorem SecurityGame.secureAgainst_of_reduction_withCost
    {g : SecurityGame Adv} {g' : SecurityGame Adv'}
    {isEff : Adv → Prop} {isEff' : Adv' → Prop}
    (R : ReductionWithCost Adv Adv' ω κ κ')
    (hadv : ∀ A n, g.advantage A n ≤ g'.advantage (R.reduce A) n)
    (hmapEff : ∀ A, isEff A → isEff' (R.reduce A))
    (hsecure : g'.secureAgainst isEff') :
    g.secureAgainst isEff := ...
```

The simplest first version can keep `isEff` / `isEff'` abstract.
Later versions can specialize them to concrete asymptotic classes built from resource profiles.

## Why This Matches The EasyCrypt Paper

This design matches the paper at the right level:

- `intrinsic` corresponds to EasyCrypt's intrinsic runtime;
- `usage` corresponds to their symbolic abstract-call counts;
- `instantiate` corresponds to their transformed complexity restrictions;
- the composition theorems explain why cost bounds compose under reductions and UC-style contexts.

The main difference is implementation strategy:

- EasyCrypt bakes this into module restrictions and a cost Hoare logic for open modules;
- VCV-io can realize the same idea semantically using `AddWriterT` and `QueryRuntime`.

## Recommended Order Of Attack

1. Add `ResourceProfile` and its algebra in a new query-tracking file.
2. Prove `eval` and `instantiate` lemmas.
3. Reify a tiny adversary interface for one-time IND-CPA.
4. Do the ElGamal example.
5. Lift the result into a cost-aware reduction theorem in `Security.lean`.
6. Use the same machinery on [Fork.lean](/Users/quang.dao/Documents/Lean/VCV-io/VCVio/CryptoFoundations/Fork.lean), where the transform becomes genuinely nontrivial.

## Open Questions

1. Should `usage` always be `κ →₀ ℕ`, or should we allow counts in another additive monoid?
   Recommendation: start with `ℕ`. This keeps substitution and repetition simple.

2. Should `intrinsic` itself later become structured?
   Recommendation: not in the first pass. If needed, let `ω` itself be a structured type.

3. Should capability indices `κ` be raw oracle domains or interface-operation enums?
   Recommendation: use interface-operation enums for theorem statements; raw query domains only when needed internally.
