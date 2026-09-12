# 05 — Direction 4: Scheduling Disciplines and the Ownership Reading of State Separation

**Claim.** Two facts already committed to the two repos, read together, resolve into one design:
(a) parallel interchange fails for lockstep `FreeM.parallel` (committed counterexample; the reason
UC frameworks need activation conventions), and (b) recursive wiring is *deliberately* not claimed
race-free absent an "affine/ownership discipline controlling shared inputs"
(`Wiring.evalParallel`'s docstring). VCVio already possesses the missing discipline in one-boundary
form: **state frames with `separated` vwb lenses — state separation by typing.** This direction
(1) makes scheduling a named, first-class hypothesis of every UC statement, and (2) promotes the
SSP frame discipline into the ownership algebra that licenses race-free wiring — the design
guardrail `composition-unification.md` flags ("state aggregation is a policy supplied by a model,
not a universal Sum or product") turned into an interface.

## 1. Scheduling: from ambient convention to named discipline

### 1.1 Current state

- Process model: one global `schedulerSampler : m (ULift Bool)` resolving every `par`/`wire`/`plug`
  interleaving node.
- Async runtime (`AsyncRuntime.lean`): a `ProcessScheduler`/`EnvScheduler` pair; synchronous
  semantics recovered by `trivialEnvScheduler` with a named equivalence theorem.
- The interchange counterexample (`aberle-parallel.md` §programs): `(g₁∥g₂)∘(f₁∥f₂) ≠
  (g₁∘f₁)∥(g₂∘f₂)` because interpretation changes synchronization. Consequence: *any* theorem that
  commutes composition with parallel interpretation is discipline-dependent.

### 1.2 Design

Introduce (PolyFun, crypto-free) a `SchedulingDiscipline` vocabulary over the parallel/interleaving
layer — data: which `∥`-ambiguities the scheduler may resolve and what it must preserve; the three
initial instances are the ones already implicitly present:

1. **lockstep** (both-blocked ⇒ joint node): what `FreeM.parallel` implements;
2. **sequential-activation** (exactly one side active; UC-style token passing): what the process
   model's binary-choice interleaving plus routing implements;
3. **env-driven** (activation chosen by an external alphabet): what `AsyncRuntime` implements.

Then three obligations:

- **Discipline-indexed statements.** `AsyncSecurity`'s theorems and `Standard.lean`'s
  `UCSecure` acquire the discipline as an explicit parameter/hypothesis. Quantifier order and
  discipline are both part of a notion's name (ground rule 3). A dishonest-but-tempting global
  "schedulers don't matter" lemma is *refutable* by the counterexample; instead prove the honest
  per-discipline invariances (e.g. sequential-activation semantics invariant under scheduler
  bias when no side is enabled — the shape `processSemantics_eq_processSemanticsAsync_trivial`
  already has).
- **Interchange up to discipline.** State and prove the restricted interchange laws each
  discipline licenses (lockstep: interchange for synchronization-preserving handlers — the
  Aberlé "additional synchronization, commutativity, or scheduling discipline" clause made into
  named lemmas). These are the lemmas `02`'s behavior model needs for its braiding/associativity
  at `wire`, so this track is a *prerequisite feed* into G-2b, not an afterthought.
- **Dummy adversary per discipline.** `HasDummyAdversaryFactor` is currently a capability record;
  derive it for sequential-activation over the behavior model (the copy-cat relay of `02` §3.2 is
  its witness). This turns the Canetti completeness-of-dummy-adversary argument into a theorem
  about one discipline rather than an axiom-shaped capability.

## 2. Ownership: state separation as the race-freedom license

### 2.1 Current state

- One-boundary (SSP): `QueryImpl.Stateful.Frame σ σ₁ σ₂`
  (`OracleComp/SimSemantics/StateT/StateSeparating.lean:64`) — two vwb `PFunctor.Lens.State`
  lenses into a joint state with a `separated : PFunctor.Lens.State.IsSeparated left right`
  field: updates don't cross, updates commute. Consumed by `linkWith` (`:222`) and `parSumWith`
  (`:462`).
- Two-boundary (UC): shared state (global RO, common reference string) has *no* story: the
  composition-unification memo explicitly rules out disjoint-union defaults, and
  `Wiring.evalParallel` exposes absence-of-contraction by duplicating inputs.

### 2.2 Design

The observation that makes this cheap: **`separated` is a separation algebra in lens clothing.**
Two commuting, non-interfering vwb lenses into σ are exactly a disjointness witness in the sense
of separation logic (compare Iris's camera composition — see `07`: iris-lean is in the workspace).
So:

1. **PolyFun**: `OwnershipFrame` on a family of state lenses (n-ary `separated`, pairwise +
   framing); theorem: a `Wiring` whose shared inputs are covered by an `OwnershipFrame` admits
   the contraction `evalParallel` refuses generically — i.e. *frame-licensed wiring is race-free*
   (statement shape: the two orders of resolving a shared input yield equal displayed handlers).
   This is the suite's most novel single theorem target; it has no analogue in EasyUC/SSProve.
2. **VCVio**: global/shared functionalities (the global-RO story of UC-with-RO / Global-RO
   papers) modeled as a component *owned by neither party* with lens access for both — frames
   express "both may read the RO cache; neither owns it exclusively; writes commute by
   freshness". The RO-cache display of `04` §3.1 supplies the freshness invariant; the frame
   supplies the ownership. Pilot: state (not necessarily fully prove) GUC-style commitment
   impossibility/possibility *shapes* to validate the interfaces against the literature.
3. **Convergence with SSP**: `linkWith`'s frame and the UC wire's frame become the same
   structure at different arities, discharging decision D2's "one layer" claim at the state
   level (Direction 2 discharged it at the experiment level).

## 3. Integration levers (order)

| Step | Repo | Deliverable |
|---|---|---|
| 1 | PolyFun | `SchedulingDiscipline` + the three instances + restricted interchange lemma pack |
| 2 | VCVio | discipline-index `AsyncSecurity`/`Standard` statements (no semantic change — naming pass) |
| 3 | PolyFun | `OwnershipFrame` + frame-licensed race-free wiring theorem (R-5.2) |
| 4 | VCVio | shared-RO as unowned framed component; connect to `04` cache display (R-5.3) |
| 5 | VCVio | dummy-adversary derivation over behavior model for sequential activation (feeds `02`) |

## 4. Rent tests

- **R-5.1**: every `AsyncSecurity` theorem names its discipline; the trivial-scheduler
  equivalence becomes an instance of a discipline-refinement lemma, not a standalone.
- **R-5.2**: the race-free-wiring theorem exists and `Wiring.evalParallel`'s "deliberately not
  claimed" docstring is upgraded to cite it as the licensed case.
- **R-5.3**: one shared-oracle UC statement (both parties query one RO) formalized without a
  hand-rolled joint-state Sum; the frame supplies the state algebra.
- **Kill criteria**: if the restricted interchange lemmas for sequential-activation resist proof
  at the free level, `02`'s G-2b inherits the risk — surface immediately (these two tracks share
  a fate). If `OwnershipFrame` duplicates what Iris-lean would give over `evalDist` for less
  cost, record the comparison and consider building on iris-lean instead (workspace has it;
  `07`).

## 5. Honest column

- Nothing here makes adversarial scheduling *easier* than in EasyUC — it makes the cost explicit
  and pays it once per discipline instead of once per theorem. If per-discipline lemma packs grow
  beyond a screen each, that claim is failing.
- The separation-algebra reading of `separated` is a design isomorphism, not a formal one, until
  the n-ary frame is defined; do not cite it as a theorem before then.
- Global-functionality modeling (GUC) is a known tar pit; the pilot is interface validation, not
  a GUC formalization commitment.
