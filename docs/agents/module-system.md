# Module Boundaries and the PolyFun Façade

This guide records the intended long-term boundary between PolyFun and VCVio
under Lean's module system. It is the decision record for visibility,
`import all`, and the `OracleComp`/`PFunctor.FreeM` relationship.

The normative language behavior is described by Lean's
[Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
reference. In particular:

- a plain `import` exposes the dependency's public scope only in the importing
  module's private scope;
- a `public import` also re-exports that public scope;
- `import all` exposes the imported module's private scope;
- a public definition is opaque to importers unless its body is deliberately
  exposed; and
- the type of a public declaration may mention only public names.

## Architectural decision

VCVio is a thin, opinionated façade over PolyFun, rather than either a second
generic free-monad library or a sealed wrapper that hides PolyFun completely.

PolyFun owns domain-independent structure:

- polynomial functors, lenses, handlers, and `PFunctor.FreeM`;
- reusable handler transformations such as target lifting, before/after
  instrumentation, and writer tracing;
- interaction trees, observations, fairness predicates, processes, and UC
  structural laws; and
- public equations needed to reason about those abstractions without opening
  private definitions.

VCVio owns cryptographic specialization:

- `OracleSpec`, `OracleQuery`, `OracleComp`, `QueryImpl`, and established
  oracle notation;
- PMF/SPMF and support semantics, probability lemmas, uniform-oracle policy,
  query accounting, and program logic;
- cryptographic games, reductions, and examples; and
- compatibility names that keep existing oracle-facing developments stable.

Generic code should accept `PFunctor`, `PFunctor.Handler`, or
`PFunctor.FreeM` directly. Oracle- and cryptography-facing code should use the
VCVio names. `OracleComp spec` remains definitionally the free monad on
`spec.toPFunctor`, and `QueryImpl` compatibility operations are thin aliases
of the generic handler operations.

Probability semantics are PFunctor-parametric but remain in VCVio: PolyFun is
domain-independent and should not acquire VCVio's PMF/SPMF policy. The
`OracleSpec.IsProbabilitySpec` name is a definitional façade over
`PFunctor.IsProbabilitySpec`; the stronger oracle uniformity bundle keeps its
existing finite/inhabited oracle instances and has an explicit
`IsUniformSpec.toPFunctor` conversion.

Do not add a conversion instance whose target is headed by the reducible
expression `spec.toPFunctor`. Such an instance can unify with unrelated
polynomial functors and pollute generic typeclass search. Prefer a definitional
alias when the concepts are identical, or an explicit conversion when they
are not.

## Import policy

Never use `import all PolyFun.…` in this repository. If VCVio needs a PolyFun
implementation detail, add an intrinsic public law or a deliberately exposed
definition to PolyFun, then use a plain or public import. The script
`scripts/check-polyfun-boundary.sh` enforces this package boundary.

Within one package, `import all` is still available for a proof module that
proves a public API theorem about a private implementation in a sibling
module. It is not a substitute for an application theorem that ordinary
consumers will also need.

Choose imports as follows:

| Need | Import form |
| --- | --- |
| Dependency used only by this module's implementation or proofs | `import` |
| Dependency appears in the public API or should be re-exported | `public import` |
| Exported tactic/elaborator dependency | `public meta import` |
| Same-package proof of a deliberately private implementation | `import all` |

## Public definitions and definitional equality

Default to an opaque public definition plus public equations. Typical API
laws are constructor equations, application lemmas, extensionality lemmas,
and characterization `…_iff` theorems. Mark a definition `@[expose]` only when
downstream definitional equality is an intentional part of the API and a
theorem would materially obstruct ordinary use.

### Visibility and transparency are separate

Four mechanisms that are easy to conflate control different parts of an API:

| Mechanism | Question it answers |
| --- | --- |
| `public` / `private` and the import form | May the importing module name the declaration? |
| `@[expose]` | Is the body available to an ordinary importer for reduction? |
| `@[reducible]`, `@[instance_reducible]`, `@[implicit_reducible]` | At which `isDefEq` transparency modes may an available body unfold? |
| Public equations | Can clients cross the boundary propositionally without unfolding it? |

An exposed body is not necessarily reducible during proof automation, and a
reducibility attribute cannot make an unavailable body appear. Likewise,
`import all` can make same-package implementation declarations available, but
does not change their reducibility status. It therefore cannot repair a term
that is well-typed only at a stronger transparency mode. Both
`PolyFun.PFunctor.Basic` and `VCVio.OracleComp.OracleSpec` deliberately expose
their relevant definitions, so the coproduct problem is a reducibility and
normal-form problem, not a module import problem.

Lean's useful transparency ladder here is:

- `.reducible` unfolds only `@[reducible]` declarations and is used for many
  speculative matches in tactics;
- `.instances` additionally unfolds `@[instance_reducible]` declarations,
  including ordinary instance definitions;
- `.implicit` additionally unfolds `@[implicit_reducible]` declarations and
  is used to check implicit and instance-implicit arguments; and
- `.default` also unfolds ordinary semireducible definitions and is used when
  checking user-written terms more aggressively.

Broader reducibility is not automatically better. In particular, definitions
that determine typeclass discrimination keys must not be made locally
reducible after their instances have been indexed. Prefer the narrowest stable
normal form that makes the intended dependent types well-formed.

### Implicit transparency in Lean 4.33

With `backward.isDefEq.respectTransparency.types` enabled, the type of a value
assigned to a metavariable must itself check at `.implicit` transparency. A
goal can therefore elaborate at `.default`, yet be unusable by `rw`, `simp`,
or a tactic-generated metavariable because a dependent type still needs an
ordinary semireducible wrapper to unfold. This is a useful invariant: it finds
terms whose apparent type correctness depended on proof automation silently
using a much stronger transparency mode.

For a focused diagnosis, put the smallest reproducer under:

```lean
set_option linter.tacticCheckInstances true

example ... := by
  ...
```

The linter checks every tactic goal at `.implicit` and reports ordinary
definitions that only the successful `.default` check unfolded. Fix the owner
of the unstable normal form. Depending on whether unfolding is part of the
API, that normally means using a public equation, spelling a primitive
dependent recursor directly, or marking the smallest intentional wrapper with
the appropriate reducibility attribute. Do not globally change the status of
core eliminators, disable the transparency check, or use `import all` as a
substitute.

Use `#guard_msgs` only when the test is meant to preserve an expected
diagnostic; do not wrap a passing regression canary with it.

### The PolyFun–OracleSpec coproduct seam

`OracleSpec ι` intentionally remains the dependent family `ι → Type`, while
`spec.toPFunctor` packages the same data as `⟨ι, spec⟩`. This middle ground is
useful: oracle code gets `Domain`, `Range`, function application, and existing
typeclass indices, while generic code gets the actual `PFunctor`. The
`toPFunctor` / `ofPFunctor` round trips are definitionally equal, so a new
wrapper structure or a wholesale conversion to `PFunctor` would add migration
cost without strengthening the abstraction boundary.

The sensitive operation is coproduct. A nested handler response contains a
type such as

```lean
((spec₁ + spec₂) + spec₃).Range (.inl (.inr t))
```

PolyFun previously represented its direction family through the ordinary
wrapper `Sum.elim P.B Q.B`. Reducing the displayed type then crossed the
oracle `HAdd` projection, the PFunctor `HAdd` projection, and `Sum.elim` before
reaching the primitive dependent recursor. The last wrapper is semireducible,
so the chain could stop at `.implicit`.

`PFunctor.sum` now writes `Sum.rec` directly and publishes its position and
branch-direction equations. The OracleSpec `HAdd` is a plain instance, so the
`instance` command gives it `instance_reducible`, and its body calls
`PFunctor.sum` by name. Using the overloaded `+` inside that instance would
insert another `HAdd.hAdd` projection into the instance's own dependent type;
naming the construction directly keeps the instance well-typed at
`.implicit`.

The instance's exact status matters. Explicitly changing it to
`@[implicit_reducible]` removes the `instance_reducible` status used during
instance unification, while changing it to `@[reducible]` makes ordinary
`simp` matching unfold combined specs and destabilizes established support
normal forms. The default instance status occupies the required middle
ground. No global attribute on `Sum.elim`, `Sum.rec`, or `HAdd.hAdd` is needed.

This change is deliberately limited to binary coproduct. `PFunctor.sigma`,
`PFunctor.pi`, products, and their OracleSpec façades also build dependent
families and should be audited with concrete canaries when they appear in
implicit-transparency diagnostics. They are not changed merely because their
definitions look structurally similar.

### How Lean core and Mathlib handle similar cases

Lean core's transparency documentation specifically recommends
`@[implicit_reducible]` for operations used in type parameters and for the two
sides of public `rfl` laws. Core monad transformers such as `StateT`, `OptionT`,
and `ReaderT` follow that pattern. Mathlib applies it selectively as well:
`Quiver.Hom.op` / `Quiver.Hom.unop` are implicit-reducible coercion wrappers,
and `AlternatingFaceMapComplex.obj` is an implicit-reducible construction whose
structure projections occur in dependent categorical types.

Mathlib also contains scoped `backward.isDefEq.respectTransparency... false`
blocks around compatibility-sensitive declarations, especially in categorical
code, so there is precedent for local migration shims. Those blocks document
remaining debt rather than providing a good library boundary for this case:
the PolyFun coproduct has a small intrinsic normal form that works with the
check enabled. `MathlibTest/TacticCheckInstances*.lean` exercises the same
linter used by the canaries here.

`PFunctor.Handler.liftTarget` is one deliberate transparent exception. Its
pointwise reduction changes only the target monad, and dependent handler
result types need that reduction during elaboration; an application theorem
alone leaves casts that Lean's rewriting tactics cannot always normalize.
The effectful `preInsert` / `postInsert` and tracing combinators remain opaque
and are consumed through their public application and factorization laws.

The compatibility migration uses broad `@[expose] public section`s so current
downstream proofs continue to elaborate. New code should expose individual
definitions instead. Over time, replace broad exposure with explicit laws and
opaque boundaries, module by module, with downstream canaries in place.

When a former `rfl` proof stops working after an import is made public-only,
do not reach immediately for `import all`. First determine which public law is
missing. A small `apply`, `…_iff`, or constructor equation usually documents
the abstraction better and makes all downstream users independent of the
implementation.

Treat a terminal `rfl` immediately after a boundary `rw` or `change` as the
same diagnostic: the public equation got the proof close, but did not produce
the intended public normal form. Close the remaining step with the relevant
application, composition, or extensionality law, or add that law at the owning
module boundary. Constructor equations and definitions whose reduction is an
intentional documented API may still use `rfl` directly.

## The Loom import boundary

The pinned `loom2` fork supplies the Loom-style `WP`/`Triple` abstractions
and the `ℝ≥0∞`/`Prob` lattice instances the program logic runs on. Its blast
radius is kept explicit so the migration to core's WP layer (`Std.WP`, once it
is public) touches a known set of files. `Loom.*` may be imported only by:

- `ToMathlib/Control/Monad/RelWP.lean`;
- `VCVio/ProgramLogic/Unary/Loom/Qualitative.lean`,
  `VCVio/ProgramLogic/Unary/Loom/Quantitative.lean`, and
  `VCVio/ProgramLogic/Unary/Loom/Probabilistic.lean`; and
- `VCVio/ProgramLogic/Tactics/Unary/Internals.lean`.

Everything else reaches Loom through those modules' public surface. A new
`import Loom.…` elsewhere is a review blocker unless it comes with an entry
here and a reason the existing bridges cannot carry it. This is a convention
enforced at review, not a script.

## Restoring `private` correctly

The module migration changed the meaning of `private`: a public exposed body
cannot retain a reference to a private declaration. Classify each affected
declaration before changing visibility.

1. If it appears in a public type, theorem statement, default argument, or
   deliberately exposed body, it is part of the public dependency closure.
   Give it an intentional public name and docstring, or redesign the public
   declaration so the helper no longer appears.
2. If it is used only in proofs, keep it `private`. Public theorem proofs are
   private module data and may use private proof helpers.
3. If it is an executable helper used only by a public runtime entry point,
   keep the helper `private` and make the entry point opaque when downstream
   callers do not need to unfold it.
4. If it is local example or test scaffolding, keep it private unless the
   example explicitly demonstrates that declaration as reusable API.
5. If callers genuinely need to reduce through it, expose the smallest
   definition and cover it with public laws. Do not enable
   `backward.privateInPublic` or `backward.proofsInPublic`.

Renaming a private helper merely to make it public avoids a name collision but
does not answer whether it belongs in the API. Record intentional promotions
in review; restore all other helpers using the patterns above.

## Validation and coordinated rollout

The boundary has three canaries:

- `scripts/check-polyfun-boundary.sh` rejects cross-package private imports;
- `VCVioTest/PFunctorFacade.lean` exercises the direct PFunctor API and the
  OracleSpec compatibility API; and
- the downstream scratch-consumer CI job imports the generic semantics and
  checks the public handler operations.

Changes that add PolyFun API and consume it from VCVio require two coordinated
repository changes:

1. merge and release the PolyFun public API;
2. update VCVio's PolyFun revision;
3. merge the VCVio aliases, proofs, and canaries.

During local development, test VCVio against the matching PolyFun worktree,
but do not merge a VCVio revision that refers to unpublished PolyFun names.
