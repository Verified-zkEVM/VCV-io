# Gotchas and Troubleshooting

## Critical (Will Bite You Immediately)

### 1. Probability semantics require the right spec class

Any file using `evalSPMF`, `probOutput`, `probEvent`, or `Pr[...]` on `OracleComp spec` needs `[IsProbabilitySpec spec]`. `evalDist` / `𝒟[…]` also needs a `MeasurableSpace` on the result type. Lemmas that use uniform cardinalities, `PMF.uniformOfFintype`, or connect `support` to nonzero probability need `[IsUniformSpec spec]`. Plain `support` works on arbitrary `OracleComp spec`.

**Symptom**: "failed to synthesize instance" mentioning `MonadLiftT (OracleComp spec) SPMF`, `IsProbabilitySpec`, `IsUniformSpec`, or `EvalDistCompatible`.

**Fix**: Add `[IsProbabilitySpec spec]` for arbitrary per-query probability semantics, or `[IsUniformSpec spec]` for uniform oracle semantics. If you already have `[spec.Fintype] [spec.Inhabited]` and want uniform sampling, install a local instance with `IsUniformSpec.ofFintypeInhabited spec`.

### 2. `autoImplicit = false` is set globally in `lakefile.lean`

Every variable must be explicitly declared. Do not rely on Lean's auto-implicit mechanism,
and do not add `set_option autoImplicit false` in individual files.

**Symptom**: "unknown identifier" for variables you expected Lean to infer.

### 3. `evalSPMF` is `simulateQ`; `evalDist` is measure-valued

`evalSPMF` is `simulateQ` with `m = PMF` and the `IsProbabilitySpec.toPMF` query implementation. Under `[IsUniformSpec spec]`, those query distributions are propositionally the uniform distributions. The `evalSPMF_eq_simulateQ` identity is definitional (`rfl`). The primary `evalDist` is the successful-output measure façade; on discrete free programs it agrees with the direct `FreeM.denote` fold.

### 4. `++ₒ` is dead — use `+`

The README and large amounts of commented-out code use `++ₒ` for combining oracle specs. The current API uses standard `+` (`HAdd`).

### 5. Delete obsolete commented-out code

Do not keep large commented-out Lean blocks around as reference material,
especially if they use obsolete patterns (`[= x | ...]`, `++ₒ`, `simulate'`,
`getM`, `guard` via `Alternative`). Delete them instead. This is distinct from
unfinished live proof attempts, which should be preserved with `stop`.
Use `Examples/OneTimePad/Basic.lean` as the canonical reference for current style.

## Type System

### 6. `query` resolves to `HasQuery.query`; use `spec.query` for the primitive

The bare `query` identifier is the `export`ed `HasQuery.query`, so writing `query t : OracleComp spec _` produces a monadic value directly and works with `evalSPMF`. The primitive single-query syntax `OracleQuery spec _` is `OracleSpec.query` (marked `protected`); reach it via dot notation `spec.query t` (or the fully qualified `OracleSpec.query t`) when you need to apply `liftM`, project `OracleQuery.cont`, or pattern-match on the query structure.

### 7. Core types are thin wrappers with deliberate reducibility

`OracleSpec`, `QueryImpl`, `OracleComp`, `OracleQuery`, and
`OracleSpec.toPFunctor` are thin `def`/`abbrev` façades over `PFunctor`
machinery. Their reducibility statuses differ according to where elaboration
needs them, and the `Monad`/`Functor` instances come directly from
`PFunctor.FreeM`/`PFunctor.Obj`. Lean may unfold them aggressively. Use
`OracleComp.inductionOn` / `OracleComp.construct` as canonical eliminators
rather than pattern matching on `PFunctor.FreeM.pure`/`roll`.

Two failure modes to recognize under this regime:

- **Dot notation on monadic results fails.** The inferred type of `oa >>= ob` or `liftM (query t)` has head `PFunctor.FreeM`, not `OracleComp`, so `(query t >>= oa).myOracleCompLemma` reports `Invalid field … PFunctor.FreeM.myOracleCompLemma`. State such lemmas in prefix form (`myOracleCompLemma … (query t >>= oa)`); dot notation on plain variables of ascribed type `OracleComp spec α` still works.
- **Never `attribute [local reducible]` a definition that instance keys mention.** Instance discrimination-tree keys are computed at declaration site; changing transparency locally makes queries normalize differently and instances like `MonadLiftT (OracleComp spec) SetM` silently vanish (`support`, `evalSPMF`, `Pr[…]` all stop elaborating). `toPFunctor` is globally reducible for exactly this consistency reason.

Relatedly, `OracleSpec.toPFunctor_add` is deliberately **not** `@[simp]`: `toPFunctor` occurs inside the instance-carrying type of an `OracleComp`, and rewriting `(spec + spec').toPFunctor` under a `simulateQ`/`liftM` strands goals in a form the `simulateQ_query` family can no longer match (typically visible as `simulateQ impl (liftM (query (Sum.inl t)))` refusing to simplify).

Nested sums are a dedicated implicit-transparency boundary. `PFunctor.sum`
uses the primitive dependent `Sum.rec`, and the OracleSpec `HAdd` instance
calls that construction directly. Keep the latter at the ordinary
`instance_reducible` status supplied by the `instance` command: making it
implicit-reducible obstructs instance-mode normalization, while making it
fully reducible changes ordinary simp normal forms. Do not replace the direct
construction with a `Sum.elim` wrapper or use overloaded `+` inside the
`HAdd` implementation: both add a semireducible/projection layer to response types such as
`((spec₁ + spec₂) + spec₃).Range (.inr t)`. If a similar failure appears,
enable `linter.tacticCheckInstances` on a minimal canary and fix the owning
combinator rather than adding global reducibility attributes or a transparency
compatibility option. Use `#guard_msgs` only when the canary documents an
expected diagnostic, not when it guards successful elaboration.

### 8. Concrete subtype samplers built with `Fintype.ofFinite` can be whnf-hostile

Subtype-uniform samplers and similar definitions sometimes close over noncomputable instances:

```lean
letI : Fintype {v // P v} := .ofFinite _
letI : SampleableType {v // P v} := .ofFintype _
```

If elaboration later unfolds this concrete sampler, `SampleableType.ofFintype` runs through
`ofEquiv (Fintype.equivFin α).symm` into `$ᵗ (Fin (Fintype.card α))`. The `Fin` instance can
then force whnf of `Fintype.card` applied to a `Classical.choice`-backed
`Fintype.ofFinite` value and hit a recursion or heartbeat limit. This is not a reason to avoid
`Fintype.ofFinite` generally; the problem is forcing reduction through a concrete closure that
captures it.

**Symptom**: a `maxRecDepth` or heartbeat timeout appears when a structure is written with
`where` field syntax, or when the concrete sampler occurs in a binder or expected-type
position, even though the same fields elaborate separately.

**Workarounds** (use only the one that avoids the observed reduction):

- Try the anonymous constructor `⟨…⟩` when `where` syntax forces normalization of the expected
  structure type.
- If a theorem statement itself forces the concrete value, quantify over an abstract value and
  pin it with an equality such as
  `(stmsis : Problem …) (hStmsis : stmsis = concreteValue)`. Use this only when callers can
  discharge the equality directly; it is an interface workaround, not an extra mathematical
  assumption.
- If elaborating or reducing `decide` over a large proposition selects an expensive
  computational `Decidable`, pass `Classical.propDecidable` explicitly. For example, use
  `@decide_eq_true_iff _ (Classical.propDecidable _)` when rewriting an accompanying `iff`
  lemma instead of asking Lean to reduce the decision procedure.

### 9. Universe polymorphism

`OracleComp` has 3 universe parameters, `SubSpec` has 3 (`u, v, w`: indices `ι : Type u`, `τ : Type v`, shared response universe `w`). Universe unification errors are still common when composing specs or building reductions because the lens-style `MonadLift` parent can drag extra metavariables in.

**Fix**: Use `{ι : Type*}` instead of `{ι : Type u}` to let universes resolve independently.

**How far to generalize depends on what you are writing.**

- A *local* definition, a proof-local variable, or a concrete scheme may pin `α β : Type`.
  Nothing downstream reuses it, and the pinning keeps elaboration predictable.
- A *public reusable law* — anything a downstream package will `rw`, `simp`, or `exact` —
  must be universe-polymorphic. A law that holds only at `Type 0` is not a replacement for
  the adapter a consumer would otherwise write; it is one more thing they have to work
  around. Take `{ι : Type*}` for indices and `{α : Type u} {m : Type u → Type*}` for the
  value universe and target monad.

The composition surface already spells the shape to copy: `QueryImpl.parallelStateT`
(`VCVio/OracleComp/SimSemantics/StateT/Basic.lean`), `QueryImpl.addReaderT`
(`.../ReaderT/Basic.lean`), `QueryImpl.parallelWriterT` (`.../WriterT/Basic.lean`), and
`VCVio/OracleComp/SimSemantics/Append.lean`. The constraint is always the same: **arbitrary
index universes, one shared response universe, and `α` in that response universe** —
`spec₁ + spec₂` goes through a dependent `Sum.rec`, which forces the response universes to agree but
leaves the index universes free, and `simulateQ` forces `α` into the target monad's source
universe.

When adding such a law, add a nonzero-universe consumer alongside it. `VCVioTest/UniversePolymorphism.lean`
is the in-repo canary, and the downstream scratch-consumer CI job builds one from outside
the package.

## Proof Patterns

### 10. `grind`/`simp` tagging is split deliberately on probability lemmas

`probOutput_bind_eq_tsum` is `@[grind =]` but NOT `@[simp]`: `simp` won't unfold `probOutput` of a
bind, so use `rw [probOutput_bind_eq_tsum]` or `grind`.

Conversely, the support-*characterization* lemmas (`Pr[…] = 0/1 ↔ ∃/∀ x ∈ support …`,
`support = {x}`, `support = ∅`: `probEvent_eq_zero_iff`, `probEvent_eq_one_iff`, `probOutput_eq_one_iff`,
`probFailure_eq_one_iff`, `mem_support_bind_iff`, …) are `@[simp]` but deliberately **NOT** `@[grind]`.
Their RHS introduces an unbounded support quantifier that `grind` Skolemizes into fresh witnesses with
no finite grounding; tagged *together* they form a re-trigger cycle so a naive `grind` on a probability
value/event goal would *saturate and time out*. The saturation is **combinatorial** — no single lemma
saturates alone (a few that sit outside the cycle, e.g. `probEvent_pos_iff` and
`probFailure_bind_eq_zero_iff`, keep `@[grind =]`); the `probEvent_eq_one_iff` family is the cycle's
hub. Dropped from the default `grind` set, `grind` instead fails fast. If a `grind` proof genuinely
needs one, re-supply it: `grind [probEvent_eq_zero_iff]`. The directed single-variable membership
bridges (`probOutput_eq_zero_iff`, `probOutput_pos_iff`, `mem_finSupport_iff`) stay `@[grind =]`. See
*`grind` vs `simp` on Probability Goals* in [`probability.md`](probability.md) and the benchmarks
`VCVioTest/ProbabilityTactics.lean` / `VCVioTest/LongChainPrograms.lean`;
`VCVioTest/GrindFailFast.lean` gates that each dropped lemma stays dropped (and that the opt-in
still works).

Downstream escape hatches, since these tags are inherited by importing projects: `grind [-lemma]`
(disable per call), `grind only [...]` (ignore the default set), `attribute [-grind] lemma`
(unset for a file), and `grind?` (print a minimal `grind only` call).

Tagging discipline, so the split stays deliberate: an unconditional equation tagged `@[simp]` in
`VCVio/EvalDist/**` or `VCVio/OracleComp/SimSemantics/**` also carries `grind =`, unless it is one
of the characterization lemmas above (the ratio in those directories is about one to one and the
gates check both closers). `@[simp, grind]` without `=` is for definitions, where `grind` uses the
equation lemmas to unfold, not for stated equations. `grind_pattern` and `[grind hom]` are not used
yet; adopt them per lemma with a gate entry, not as a sweep.

### 11. Plain `vcstep` may solve a probability equality when you only wanted a rewrite

On `Pr[...] = Pr[...]` goals, plain `vcstep` heuristically tries swap, congruence, and
small bounded compositions. If you need to rewrite and continue, use `vcstep rw` for a
top-level swap, `vcstep rw under 1` under one shared bind prefix, or
`vcstep rw congr` / `vcstep rw congr'` to expose a shared outer bind. The manual pattern is:
```lean
simp only [← probEvent_eq_eq_probOutput ...]
rw [probEvent_bind_bind_swap]
simp only [probEvent_eq_eq_probOutput]
```

### 12. Avoid `guard` in experiments

Use `return (b == b')` or `return decide (r x w)` instead. `guard` requires `OptionT` / `Alternative`.

### 13. `do`-notation bind uses a different `Bind` instance (Lean 4.29+)

Lean 4.29 changed `do`-block elaboration so the desugared bind may use a `Bind` instance
that differs syntactically from `Monad.toBind`. This means `pure_bind`, `bind_assoc`, and
`bind_pure` won't fire via `simp` or `rw` on goals produced by `do` notation in special cases of using more non-standard instances.

**Symptom**: `simp [pure_bind]` or `rw [bind_assoc]` does nothing on a `do`-block goal.

**Fix**: Use the restated lemmas from `ToMathlib.Control.Lawful.Basic` (namespace `LawfulMonad`):
`do_pure_bind`, `do_bind_pure`, `do_bind_assoc`, `do_bind_pure_comp`, `do_map_bind`,
`do_bind_map_left`. All are `@[simp]`.

### 14. Hypothesis satisfiability is a proof obligation

A conditional theorem whose hypotheses are jointly uninhabitable is vacuously true, and
`#print axioms` cannot detect it: the proof is axiom-clean while the statement asserts nothing.
Two failure classes recur:

- **Relation-pinning pairs**: a pair `(hr : GenerableRelation _ _ r) (hGen : hr.gen = myGen)`
  is uninhabitable if some `(x, w) ∈ support myGen` has `r x w = false`, because
  `GenerableRelation.gen_sound` requires every supported pair to satisfy the relation. Check
  `gen_sound` compatibility *before* stating the theorem; if the support does not fit, widen
  the relation (e.g. an ∃-material variant of key validity) rather than pinning an incompatible
  generator.
- **Cardinality mismatches**: the deterministic image of a small seed space can never equal —
  or be uniformly distributed on — a strictly larger space. A hypothesis asserting such an
  equality or uniformity is false at every parameter where the strict cardinality inequality
  holds.

**Fix**: when compatibility of a new hypothesis bundle is not immediate, ship a kernel-checked
witness for the whole bundle (or at least each nontrivial compatibility pair) in the same PR.
For example, prove `∃ hr, hr.gen = …` with an explicit witness rather than merely showing each
hypothesis type is separately inhabited. A toy witness establishes logical consistency only;
label it accordingly and do not present it as evidence that the assumptions are
cryptographically strong or achievable at real parameters.

## Module Structure

### 15. `EvalDist/` must never import from `OracleComp/`

Check the module layering DAG before adding imports:
```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → {ProgramLogic, CryptoFoundations, CryptoFoundations/Asymptotics} → Examples
```

### 16. Preserve partial proof attempts with `stop`

When a proof attempt is not finished or is currently broken, insert a local `stop` marker instead of deleting large proof blocks. This preserves search context for later agents.

### 17. `OracleComp.inductionOn` is the canonical eliminator

Pattern: `| pure x => ... | query_bind t oa ih => ...`. Use `simulateQ_bind`,
`simulateQ_query`, `simulateQ_pure` simp lemmas in the `query_bind` case.
See `simulateQ_id'` in `VCVio/OracleComp/SimSemantics/SimulateQ.lean` for a
clean example.

### 18. Full cutover, no backward-compatibility shims

When refactoring APIs, notations, or proof infrastructure, update all call sites in one
pass. Do not add deprecated aliases, migration wrappers, or compatibility layers.

### 19. Module organization: no thin re-export umbrellas except at the repository top level

When splitting a file into a folder of submodules, do **not** add a sibling `X.lean`
whose only content is a chain of `import X.A; import X.B`. Each caller imports the
specific submodule it actually uses.

**Allowed umbrellas** (strictly top-level roots only): root imports such as
`VCVio.lean`, `ToMathlib.lean`, `Extern.lean`, `HashSig.lean`, `Examples.lean`,
`LatticeCrypto.lean`, `Interop.lean`, `VCVioWidgets.lean`, `VCVioTest.lean`, and
`LatticeCryptoTest.lean`.
When a new top-level root is added, extend this list alongside it.

**Not allowed**: umbrellas inside a subdirectory (e.g. a top-level
`VCVio.CryptoFoundations.FiatShamir` umbrella beside the `VCVio/CryptoFoundations/FiatShamir/`
folder, or a `VCVio.OracleComp` umbrella beside the `VCVio/OracleComp/` folder). Even if a module "feels
cohesive", callers must import the specific submodule they use.

## Build and Tooling

### 20. Always run `lake exe cache get` before `lake build`

Building Mathlib from source takes hours. Always fetch the precompiled cache first.

### 21. Warm-start new worktrees from a built donor worktree

`lake exe cache get` only covers Mathlib; the repo's own libraries still rebuild from scratch
in a cold `git worktree`. When two worktrees use the same toolchain, dependency revisions, and
preferably the same commit, copying the root build tree from an already-built donor can make
the target's next build a near-no-op. Do this before the target has its own `.lake/build`;
the explicit check prevents `cp` from nesting or merging build directories accidentally:

```bash
mkdir -p "<new-worktree>/.lake"
test ! -e "<new-worktree>/.lake/build"
cp -a "<built-donor-worktree>/.lake/build" "<new-worktree>/.lake/"
```

Run `lake exe cache get` in the target as usual, then run `lake build` so Lake checks the copied
artifacts against the target sources and rebuilds anything affected. If Mathlib itself starts
rebuilding at scale, stop and check the toolchain, dependency revisions, and whether the
Mathlib cache was fetched; copying the root build tree does not replace the Mathlib cache.

### 22. Direct Lean and the LSP can observe stale imported oleans

`lake env lean File.lean` invokes Lean directly; it does not ask Lake to rebuild imported
modules first. The language server can likewise consume the compiled imports already on disk.
After mid-edit builds, branch switches, or source changes outside the file being checked, those
imports can be stale. Elaborating against mismatched imports can produce phantom failures that
mimic genuine elaboration pathologies:

- whnf/heartbeat timeouts that no `maxHeartbeats` bump cures because nominally matching terms
  came from different compiled source states;
- "unknown identifier" and "has already been declared" errors for declarations that match the
  source in front of you;
- apparent section-dependence, where sharing local instance variables happens to avoid the
  mismatched imported term and makes the symptom disappear inside a section.

**Fix**: before diagnosing an elaboration problem involving imported declarations or
instances, run `lake build <target>` to synchronize the affected modules, then reproduce the
problem with `lake env lean` or the LSP. The build may be a no-op when the imports are already
current; only trust the suspected stale-import symptom if it survives this check.

### 23. Do not disable linters to silence warnings

Do not add `set_option linter.* false`, `set_option weak.linter.* false`, or repo-level
`leanOptions` that turn lints off just to get a clean build. Treat linter failures as real
problems and fix the underlying declaration, proof, naming, or formatting issue instead.

The one deliberate, documented exception is the text-based unicode allowlist linter, turned
off via `weak.linter.unicodeLinter, false` in `lakefile.lean`. This is a policy choice, not a
dodge: VCVio docstrings legitimately use FIPS-204 math notation (a combining tilde on `c`) and
diacritics in cited author names, which the Mathlib allowlist would otherwise reject.

### 24. After adding new `.lean` files, run `./scripts/update-lib.sh`

This regenerates the active module root files covered by the build import check:
`ToMathlib.lean`, `VCVio.lean`, `LatticeCrypto.lean`, `Extern.lean`,
`HashSig.lean`, `Examples.lean`, `VCVioWidgets.lean`, and `VCVioTest.lean`.
It also updates the legacy `Interop.lean` umbrella without enabling module mode.
CI checks the active module roots; `Interop` remains dormant and is migrated separately.

### 25. Active Lean sources use explicit module scopes

Start active source files with `module`, use public imports deliberately, and put declarations in
`public section` or `public meta section`. Existing ordinary files use `@[expose] public section`
for downstream compatibility; executable and runtime implementation modules should use opaque
`public section` when downstream code does not need definitional unfolding. Never reach for
`backward.privateInPublic` or
`backward.proofsInPublic`; make helper visibility explicit or give proof terms enough type
information to avoid public metavariables.

The dormant `Interop` library is intentionally excluded until its separate migration.
`LibSodium/SHA2.lean` is also excluded because it is a dormant source outside every Lake library.
`LatticeCryptoTest.lean` remains a curated umbrella and `HashSigTest` has no root umbrella because
their executable modules contain colliding root-level `main` declarations.

### 26. Lean toolchain and Mathlib version must stay in sync

Both currently `v4.33.1`: `lean-toolchain` pins `leanprover/lean4:v4.33.1` and
`lakefile.lean` has `require "leanprover-community" / "mathlib" @ git "v4.33.1"`.
When upgrading, update both lines simultaneously.

### 27. Use public references in shared docs

When a proof framework follows an external paper, cite the public paper by title, venue,
or URL rather than pointing agents at a repo-local file path.

### 28. Public reference papers are authoritative for design work

For relational program logic, start with
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25)).

### 29. Agent guidance files must be committed

Agents dispatched to `git worktree` clones need to read `AGENTS.md`, `docs/agents/`, and any other guidance files. Ensure these are committed so all worktrees see them.

### 30. Restack with `--onto` after folding commits into a base branch

When a stacked branch's base is cherry-picked or squashed into a new base, the old base commits
may not be ancestors of the new base. Record the old base tip and the pre-rebase branch tip,
then select only the branch-owned commits explicitly:

```bash
git rebase --empty=drop --onto <new-base> <old-base-tip> <branch>
```

Inspect how those commits were replayed before pushing:

```bash
git range-diff <old-base-tip>..<pre-rebase-tip> <new-base>..<rebased-tip>
```

Conflict resolutions or commits made empty by the new base can produce legitimate differences,
so review the range diff and rerun the relevant build/tests. A final-tree byte-identity check

```bash
git diff <pre-rebase-tip> <rebased-tip> --quiet
```

is an additional strong gate only when the new base differs from the old stack solely by
folding the same content. Do not require tree identity when the new base also contains unrelated
changes; those changes should appear in the rebased tree.
