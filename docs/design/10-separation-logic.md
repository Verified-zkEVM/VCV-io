# 10 — Direction 6: Separation Logic over the Substrate (Iris, Bluebell, and the Ownership Algebra)

**Status: normative core (the three identifications, Track S1a/S2c), fluid periphery (everything
touching iris-lean's moving proofmode or Bluebell's unproved model).**

**Claim.** Separation logic — both the Iris lineage and the probabilistic lineage
(PSL → Lilac → Bluebell) — connects to the PolyFun substrate through three precise
identifications, not through a vague "both are categorical" gesture. Each identification pairs an
existing separation-logic structure with an existing (or already-planned) PolyFun/VCVio structure,
and each yields theorems, not analogies. Two integration tracks follow: **S1** — iris-lean as an
engine for the concurrent/UC layer (ordinary separation logic, ghost state, guarded recursion);
**S2** — Bluebell-style probabilistic BI as a new relational carrier over `evalDist`
(independence and conditioning as first-class proof moves). Neither track replaces Loom or the
displayed logic of `04`; both plug into the bridge-theorem discipline of decision D3.

## 1. The three identifications (the "common ancestor," made concrete)

The folklore answer to "what do separation logic and polynomial functors have in common?" is
categorical logic: both are fibered/indexed structure over a base category of programs or
resources. That answer is true and useless. The useful answers are these:

### 1.1 Resource algebras = ownership frames

Every separation logic is parametrized by a partial commutative monoid (PCM) of resources —
Iris's cameras/CMRAs, PSL's partial monoid of independent-product-compatible probability spaces,
Bluebell's `PSpPm` (probability space × fractional permission, composition = independent product
⊗ permission sum). VCVio *already has* the structural instance: `QueryImpl.Stateful.Frame`'s
`separated` pairs of very-well-behaved lenses (commuting, non-interfering updates into a joint
state) are a PCM of state views — `05` §2.2 flags this as "a separation algebra in lens
clothing," and its `OwnershipFrame` ticket is precisely the n-ary PCM completion. So:

- **upstairs (structural, PolyFun/VCVio core):** resources = separated lens families; `P ∗ Q` =
  "the two packages own disjoint frame components";
- **downstairs (probabilistic, VCVio):** resources = probability spaces on state components;
  `P ∗ Q` = probabilistic independence (PSL's reading, Bluebell's `PSp` composition).

The theorem that makes this two-level picture load-bearing rather than decorative:

> **Frame-independence transfer (target).** If two packages act through a `separated` frame and
> their (probabilistic) initializations are independent, then the joint state distribution after
> any interleaved run remains an independent product on the frame components. Structural
> separation *upstairs* is the license for independence reasoning *downstairs*.

This is the probabilistic instance of the frame rule, and it is exactly the fact PSL's
soundness proof establishes wholesale for its toy language — here it becomes one theorem about
`runExp` over framed matter (`03`'s carrier), consumed by every S2 proof.

### 1.2 BI conjunction = joint displays over `⊗` (Day convolution, concretely)

BI's separating conjunction on assertions is Day convolution along the resource monoid. In Poly,
the analogous move already exists in the G-series: a display over `p` and a display over `q`
induce a display over `p ⊗ q` (and over `p ∥ q`'s `.both` branch) whose evidence is *jointly*
quantified — `04` §3.2 uses exactly this for `RelDisplayed`. Identification: **the
separating conjunction of two program-level invariants is their joint display over the tensor of
boundaries, and the frame rule is displayed functoriality of parallel composition, licensed by an
ownership frame (`05`).** Two consequences:

- the displayed logic of `04` is not merely "pRHL-shaped"; it is the *intrinsic* form of the BI
  layer, and any S1/S2 assertion language should compile down to displays where it touches
  program structure (bridge theorem, one per connective that crosses the boundary);
- the interchange counterexample (`05` §1) reappears here as the *expected* BI phenomenon: `∗`
  does not commute with sequential interpretation without a discipline — separation logics
  encode that as side conditions on the frame rule; we encode it as `SchedulingDiscipline`
  hypotheses. Same fact, two vocabularies; the docs should cross-cite rather than re-derive.

### 1.3 Step-indexing = finite projections of the cofree comonoid

Iris's model is built on OFEs/COFEs: types with a decreasing family of "n-equivalences," limits,
and the later modality `▷` with Löb induction. PolyFun's `Cofree/FiniteProjection` (Prop 8.49)
says a behavior is determined by its finite projections. These are the same mathematics: **the
n-th projection of a cofree mate is the n-equivalence class of the behavior; `BehaviorObj`
(`02`) carries a canonical COFE structure with `dist n b₁ b₂ := projectionN n b₁ = projectionN n
b₂`, complete by the M-type's limit property.** Under this identification:

- Löb induction over the behavior COFE *is* the coinduction principle `02` uses via `M.bisim`,
  repackaged so that iris-lean's proofmode (which speaks OFE natively) can drive it;
- guarded recursion gives `02`'s corecursive constructions (`par`/`wire`/`plug` on behaviors) a
  second implementation route: define them as guarded fixpoints, get coherence by Löb — worth
  attempting exactly if the direct `M.corec` route hits the transport-cost kill criterion in
  `02` §5;
- Iris's "later credits"/step-counting machinery lines up with `RunLimit`-style bounded execution
  (k-l-examples; `08` G-0b) — a reconciliation note, not a dependency.

## 2. Zoom-in: the Iris feature set against the crypto workload

§1 deliberately used only entry-level separation logic. This section confronts the features that
make Iris *Iris* — step-indexing, ghost state up to higher order, invariants, fancy updates —
and assigns each a crypto job or an honest "not needed yet." The organizing discovery (from
reading the Rocq probabilistic-Iris line at the source): **the coupling arguments at the heart of
game-hopping are already, in published and mechanized form, ghost-state definition and
manipulation.** That is not an analogy to be built; it is a design to be ported and then
generalized in the Bluebell direction.

### 2.1 Step-indexing does two different jobs — keep them separate

- **Job 1: guarded recursion over program execution.** Iris WPs are guarded fixpoints (recursive
  occurrence under `▷`); Clutch's probabilistic WP has exactly this shape. This is the job §1.3
  already identified with finite projections of the cofree comonoid: the behavior COFE makes
  Löb induction available for coinductive facts about open systems. Nothing new here — except
  the warning that *probabilistic* adequacy under step-indexing is where the Rocq line spent its
  real effort (Clutch's per-step coupling modality `execCoupl` and its erasure theorem), so any
  S1c-style WP must budget for the adequacy proof, not the logic.
- **Job 2: breaking the circularity of impredicative invariants and higher-order ghost state.**
  Storing arbitrary propositions in invariants or in resources forces the recursive domain
  equation `iProp ≅ uPred(Res(iProp))`, solved by the America–Rutten construction over OFEs.
  **Status correction, verified at source 2026-07-20: iris-lean has this today** —
  `Algebra/COFESolver.lean` (Carneiro–Graf, 2025) solves the domain equation,
  `Algebra/IProp.lean` builds `iProp` over `BundledGFunctors` (the `gFunctors` mechanism, so
  users register cameras exactly as in Rocq Iris), and the derived layer includes namespaced
  invariants with `inv_alloc`/accessors, fancy updates (`FUpd`, view-shift derivation),
  **cancelable and non-atomic invariants**, **later credits**, `GhostMap`, and prophecy-variable
  machinery (`ProphMap`), plus an abstract WP with adequacy over an `EctxLanguage` interface and
  a worked HeapLang instance. The earlier revision of this doc undersold iris-lean as "MoSeL +
  UPred + some RAs"; in fact the *entire* higher-order-ghost-state stack is ported or in
  reachable distance.
- **When does crypto need Job 2?** Honest triage. First-order cameras cover the bulk of
  crypto bookkeeping (§2.2). Higher-order ghost state earns its keep exactly where proofs
  quantify over *program-shaped* objects: (a) Clutch-style spec resources — the specification
  *program* lives in ghost state, and `specCtx` is an invariant holding a configuration; (b)
  logical-relations arguments — the plumbing behind a soundness proof for an Owl-style type
  system (`11` §3.3's long-range version) and Approxis's credit-quantified logical relation;
  (c) any future "environment as a logical variable" treatment of UC emulation. None of these
  are this-cycle deliverables, but (a) is next-cycle-real (§2.3), which is why S1's bridge repo
  should build against `iProp`/`gFunctors` from the start rather than against bare `UPred`.

### 2.2 The camera catalogue, read as crypto bookkeeping

Iris's second killer feature is that *protocol-specific reasoning is encoded by choosing a
resource algebra*, with frame-preserving update as the licensing judgment for ghost moves. The
catalogue that iris-lean already ships maps onto VCVio's standing bookkeeping burdens almost
line-by-line:

| Camera (in iris-lean today) | Crypto bookkeeping job |
|---|---|
| `Auth` (`●`/`◯`) | one authority, many partial views: RO cache (authoritative table vs. per-caller fragments), spec-program configuration (§2.3) |
| `GhostMap` / `HeapView` | per-entry ownership of an oracle table: RO entries as individually owned, transferable points-to facts — the fine-grained version of `QueryTracking`'s monolithic cache state |
| `Agree` | public data that all parties must concur on: transcripts, public keys, CRS |
| `Excl` / one-shot (`Csum`) | unique-event tokens: "challenge issued," "key extracted," commitment opened — the one-shot camera *is* the commit-then-open shape |
| `Frac`/`DFrac`/`UFrac` | divisible read access to shared state — the fractional refinement of `05`'s frames already anticipated in S1a |
| `MonoNat` | monotone counters: query counters with once-exceeded-always-exceeded budget facts — the ghost form of `IsQueryBound` |
| cancelable invariants (`CInvariants`) | **invariant-until-bad**: an invariant with a cancellation token is precisely the `IdenticalUntilBad` shape — cancel at the bad event, keep the token as the bad-event witness. The `11` `up_to_bad` combinator and this camera should be one design |
| later credits | amortized `▷`-elimination; bookkeeping, listed for completeness |
| `ProphMap` (prophecy variables) | reasoning *now* about values determined *later* — the deterministic ancestor of presampling tapes (§2.3); prophecy erasure and tape erasure are the same proof pattern |
| Eris-style error credits (`ℝ≥0`-valued, not yet in iris-lean) | **the advantage ledger as a resource**: `£ε` splits by union bound, is spent to exclude bad events, and the adequacy theorem converts remaining credit into a probability bound. `11`'s hop-chain ledger is this camera wearing tactic clothing — the two designs must stay isomorphic so a later unification is a refactor, not a rewrite |

The design consequence: S1a's "frame camera" is not one instance but a *policy* — each VCVio
bookkeeping idiom gets the standard camera above instead of a bespoke lemma family, and the rent
test for any single row is that the ghost version deletes the hand-rolled twin.

### 2.3 Couplings as ghost state — the load-bearing zoom

The published mechanism (Clutch, POPL 2024, read at source; CaReSL is the ancestor): to prove
`e ≾ e'`, the right-hand program is *not* part of the judgment's program position — it is a
**ghost resource** `spec(e')`, tied by an invariant `specCtx` (two authoritative camera
instances: one for the spec configuration, one for the spec heap/tapes) to the coupling built by
a *unary* WP. The refinement judgment is

```
specCtx ∗ spec(e') ⊢ wp e { v. ∃v'. spec(v') ∗ φ(v, v') }
```

and its reading is exactly the user-level slogan: **advancing the coupled program is a ghost
move** (a fancy update rewriting `spec(K[e'])`, with "run-ahead" permitted — the spec side may
be executed independently of the physical side), and choosing a coupling is a per-step
obligation inside the WP (`execCoupl`), discharged rule-by-rule. Adequacy extracts an honest
probabilistic coupling, and `μ₁ ∼ μ₂ : (=) ⇒ μ₁ = μ₂` lands distribution equality. Three
transfers for this suite:

1. **Presampling tapes are ghost seed stores — VCVio already owns the operational half.**
   Clutch's tapes `ι ↪ (N, n̄s)` exist to make couplings *asynchronous*: a ghost presampling
   step on one side is coupled with a real sampling on the other, the tape is read later, and
   the adequacy-level **erasure theorem** removes tapes from the final statement (their §2
   flagship: lazy/eager coin equivalence). VCVio's `SeededOracle`/deferred-sampling engine
   (#465) is semantically the same object *minus the logic*: seeds are presampled randomness,
   and the eager/lazy switch lemmas are hand-proved erasure instances. Deliverable shape
   (S2d below): a ghost seed-coupling layer over `SeededOracle` — couple seeds at presampling
   time, consume at query time — turning today's per-example eager/lazy lemmas into instances
   of one erasure theorem. Caution imported with the design: Clutch §7 gives counterexamples
   showing *unrestricted* presampling rules are unsound; the tape discipline is load-bearing,
   not decoration.
2. **Approximate couplings close the loop to game hops.** Approxis (POPL 2025, same family;
   acquired 2026-07-20) recasts Eris's error credits *relationally* over the same
   spec-resource architecture: hops carry `£ε`, credits compose along the chain, a limiting
   argument (`ε → 0` internally) recovers exact equivalences — and its mechanized case studies
   are **the PRP/PRF switching lemma and IND$-CPA of an encryption scheme**. That is an
   existence proof, in a proof assistant, that *game-hopping with quantitative advantages is
   ghost-state manipulation* — the strongest external validation this direction has. It also
   fixes the interface obligation on `11`: the advantage ledger and relational error credits
   must be the same accounting object viewed from tactic-land and logic-land respectively.
3. **Bluebell is the symmetric, n-ary limit of the spec-resource idea — and conditioning has a
   ghost-state reading.** Clutch is asymmetric: one physical program, one ghost program.
   Bluebell's `I`-indexed model makes *every* program's distribution a resource (there is no
   physical side), which is why it can state hyper-properties Clutch cannot; what it lacks is
   Clutch's dynamics (ghost moves, invariants, adequacy-by-erasure). The synthesis hypothesis,
   stated as such: **joint conditioning is ghost agreement** — `C^{X←x}` conditions the
   indexed resources on an outcome; operationally that is allocating an `Agree`-style witness
   of the conditioned value and reasoning under it, with the C-merge rules as agreement
   composition. If this holds even for the discrete/`SPMF` fragment, Bluebell's most exotic
   connective becomes a derived construction over standard cameras — a genuinely new result,
   and one that would make the S2 layer *definable inside* an iris-lean-based logic rather
   than a separate model. R-10.6 makes this falsifiable; it is a hypothesis, not a claim.

### 2.4 Invariants, persistence, atomicity — quick hits

- **Persistent vs. exclusive is the public/secret split.** Transcripts, public keys, and CRS
  are persistent knowledge (`□`); secret keys and one-shot capabilities are exclusive
  resources. This is vocabulary worth adopting even in prose.
- **Oracle queries are atomic by construction.** VCVio's programs interact with state only
  through handler steps, so the invariant-opening discipline (masks, atomicity side
  conditions) degenerates pleasantly: every query is a single atomic step and invariants can
  be opened around it without HeapLang's fine-grained-concurrency caveats. The async runtime
  (`05`) is where genuine interleaving returns and the full discipline earns its keep.
- **Impredicative invariants** (storing arbitrary `iProp`s) are what §2.1 Job 2 buys; the
  crypto consumer is the spec-resource invariant `specCtx` (§2.3) and, long-range,
  environment-quantified UC arguments. First-order invariants suffice for everything else
  named in this doc.

## 3. Current state (precise; audited 2026-07-20)

- **iris-lean** (workspace checkout, upstream `leanprover-community/iris-lean`): substantially
  the full Iris stack — MoSeL proofmode, `UPred`, the camera library (`Auth`, `Agree`, `Excl`,
  `Csum`, `Frac`/`DFrac`/`UFrac`, `View`/`HeapView`, `GhostMap`, `MonoNat`, `ReservationMap`),
  **the COFE solver and `iProp` over `gFunctors`** (higher-order ghost state is available, §2.1),
  namespaced/cancelable/non-atomic invariants, fancy updates, later credits, prophecy maps,
  abstract WP (#475) with adequacy over `EctxLanguage`, and a worked HeapLang instance. In-flight
  setoid→type port (#502) — the tree is moving; any consumer pins a revision. No probability
  anywhere.
- **iris-bluebell** (workspace checkout, Verified-zkEVM fork of iris-lean): Bluebell's model laid
  out in `src/Bluebell/`: `PSp` (probability-space RA), `PermissionRat`, `PSpPm` (predicated
  product), `IndexedPSpPm` (= the paper's `Hyp[I]{PSpPmRA}`), `HyperAssertion` (upward-closed
  sets), `assertSampledFrom`, the joint-conditioning modality `jointCondition`, coupling
  infrastructure, and `wp`. Honest reading (confirmed by the repo's own audit note
  `notes/rules_progress.md`): nearly all rules are `sorry`; CMRA validity/compatibility fields
  are partly placeholder; and — the load-bearing gap — **`wp` takes an opaque semantic
  transformer `t : IndexedPSpPmRat I α V → IndexedPSpPmRat I α V`; there is no program syntax or
  semantics in the repo at all.**
- **VCVio**: Loom carriers with the one-visible-carrier `outParam` discipline (`01` §1.4);
  `CouplingPost` (coupling existence over `evalDist`); quantitative `ℝ≥0∞` carrier; state frames
  with `separated` (`01` §1.3); deferred/seeded sampling (#465, `SeededOracle`); `evalDist`/
  `tvDist` layer.
- **Design sources in Rocq** (papers in paper-note): Clutch (POPL 2024), Eris, Tachis, Foxtrot —
  the mature "probabilistic Iris" family. Two direct correspondences worth stealing rather than
  reinventing: Clutch's *presampling tapes* are semantically VCVio's seeded-oracle engine
  (asynchronous couplings = coupling the seed, not the sample site); Eris's *error credits* are
  a resource-algebra rendering of the union-bound bookkeeping VCVio does by hand in
  `IdenticalUntilBad`/`Advantage` chains.
- **Papers** (all in paper-note; source-verified 2026-07-20): Bluebell (Bao–D'Osualdo–Farzan,
  POPL 2025, arXiv 2402.18708; PDF also in the fork's `paper/` directory) — its programs are
  imperative with *statically bounded* `repeat N` loops over first-order stores, assertions are
  upward-closed predicates over `I`-indexed resources (probability-space fragments paired with
  permissions — distributions over stores, ownable in pieces), and relational lifting `⌊R⌋` is
  defined as coupling-existence with the relation holding with probability 1 — the same
  mathematical object as `CouplingPost`, which is what makes the S2b bridge near-definitional in
  the qualitative case. Lineage: PSL (Barthe–Hsu–Liao, POPL 2020) made `∗` = independence via a
  new probabilistic BI model; DIBI (Bao et al., LICS 2021) added conditional independence;
  Lilac (Li–Ahmed–Holtzen, PLDI 2023) made separation = independence of σ-algebras and added a
  conditioning modality; Bluebell subsumes the line with joint conditioning over indexed
  programs.
- **One more fork caveat** (from its own `notes/rules_progress.md` audit): besides the missing
  program layer, the fork records a *known discrepancy between the paper's WP definition and
  the Lean `wp`*. S2a therefore includes aligning the WP definition with the paper (or
  documenting the deliberate divergence) as part of supplying the semantics — the bridge must
  not inherit an unexamined definition.

## 4. Design

### 4.1 Track S1 — iris-lean as engine for the structural/concurrent layer

- **S1a (entry point, cheap): the frame camera.** Package `05`'s `OwnershipFrame` as a resource
  algebra instance for iris-lean: elements = lens-frame components (with fractional-permission
  refinement for shared read access — `UFrac` is already ported upstream), composition = frame
  disjointness. Payoff: MoSeL proofmode over package states; the shared-RO/global-functionality
  story (`05` §2.2 step 2) gets Iris's ghost-state vocabulary (auth/frag for the RO cache) instead
  of hand-rolled invariants. This is also the honest execution of `05`'s kill-criterion clause
  ("if `OwnershipFrame` duplicates what iris-lean would give, build on iris-lean instead") — S1a
  *is* that comparison, run as an experiment.
- **S1b: the behavior COFE.** Define the §1.3 COFE instance on `BehaviorObj` (PolyFun ticket,
  crypto-free: it is a statement about M-types and finite projections; iris-lean dependency stays
  in a bridge repo/file so PolyFun itself does not acquire an iris dependency). Consumer test:
  re-prove one `02` coherence lemma by Löb induction and compare against the `M.bisim` proof.
- **S1c (contingent): abstract WP over `OracleComp`.** iris-lean's abstract WP (#475) is
  parameter-shaped; instantiating it at `simulateQ`-semantics would seed a "Clutch-for-Lean."
  Deliberately *not* scheduled this cycle *as a unary program logic*: Loom already occupies the
  extrinsic-WP niche, and a second ambient WP violates the spirit of the `outParam` discipline.
  Scope refinement after §2.3: S2d.1 does instantiate an Iris-style WP, but at *coupling*
  semantics (the `execCoupl` shape) as internal machinery of the ghost-coupling layer — a
  relational device discharging into `CouplingPost`, not a user-facing unary logic. The
  unary-logic version of S1c stays gated on S1a/S1b paying and a concurrency-heavy consumer
  (async runtime proofs, `05`) demanding invariants/ghost state Loom cannot express.

### 4.2 Track S2 — Bluebell into VCVio

The strategic fact: Bluebell's missing half (program semantics) is VCVio's strongest layer, and
VCVio's missing relational vocabulary (independence, conditioning) is Bluebell's core. The fit is
exact, and it is the same fit twice:

- **S2a: give Bluebell its programs.** The `wp`'s opaque transformer `t` is, in VCVio terms, the
  state kernel of a package: an `I`-indexed family of `QueryImpl.Stateful`-driven runs over a
  shared memory type (`σ := α → V` in their notation), pushed through `evalDist`. Deliverable: a
  `Semantics`-backed constructor for Bluebell transformers from indexed `OracleComp` programs +
  handler stacks, with `wp_bind`/`wp_query` laws *derived* from `simulateQ` algebra rather than
  postulated. Where it lives: a bridge library (new lake package depending on both VCVio and
  iris-bluebell), not in VCVio core — toolchain drift between the two repos is a real operational
  risk and must stay quarantined.
- **S2b: joint conditioning over `evalDist`.** Bluebell's `C` modality (conditioning a
  hyper-assertion on the value of a program variable, jointly across the indexed family) is the
  proof move VCVio currently lacks entirely: today a conditional argument is done by manually
  splitting the SPMF and re-assembling. Target: `C`-style conditioning lemmas for `SPMF`
  (downstairs, no PolyFun content), and the bridge theorem **relational lifting ⇒
  `CouplingPost`**: Bluebell's `cpl` (lifting via joint conditioning) implies the existing
  coupling-existence carrier, so every S2 proof discharges into today's ecosystem. Respecting the
  carrier discipline: the hyper-assertion layer enters as a *producer* of `CouplingPost` facts via
  this bridge — it is not registered as a third ambient Loom carrier.
- **S2c: the crypto pilots are the founding examples of the field.** PSL's warm-up is the
  one-time pad, and its case studies are private information retrieval, oblivious transfer,
  secure multi-party addition (secret-sharing style), and simple ORAM — all *independence*
  statements, all information-theoretic. Two of these already live in VCVio as pain points: OTP
  privacy (currently a coupling/`evalDist` computation) and `SimpleTwoServerPIR` (named by `01`
  §1.6 and `04` R-4.4 as a rewrite candidate). Pilot: prove OTP privacy (and one
  secret-sharing-style statement) as `key ⊥ message ⇒ ciphertext ⊥ message` in the S2 layer,
  discharged through the frame-independence transfer theorem of §1.1. **Coordination note:**
  `04` R-4.4 targets SimpleTwoServerPIR as a *relational display*; this doc's natural treatment
  of the same example is an *independence* proof. Do both only if the first lands cheaply — the
  two treatments of one example are a feature for the paper-2 comparison table, but the second
  is not allowed to become its own project. This is where "structural upstairs, distributional
  downstairs" becomes visible in a *proof style*: frame reasoning until the last step, one
  independence fact at the end.
- **S2d: the ghost-coupling layer (couplings as spec resources + seed tapes).** The §2.3
  transfer, staged to stay falsifiable:
  1. *Spec resource over VCVio programs*: define `specRes : OracleComp spec α → iProp` with the
     Clutch architecture (auth camera for the spec configuration; `specCtx` invariant; ghost
     moves = fancy updates advancing the spec program by `simulateQ` steps, run-ahead allowed),
     and prove the adequacy bridge `specCtx ∗ specRes e' ⊢ wp e {v. ∃v', specRes (pure v') ∗
     φ v v'}` ⟹ `CouplingPost e e' φ`. This *re-derives* the existing carrier from ghost
     dynamics rather than replacing it — decision D9's bridge discipline applies unchanged.
  2. *Seed tapes*: expose `SeededOracle`'s seed store as a tape resource `ι ↪ seeds` with
     presample/consume ghost rules and one erasure theorem into `evalDist`-equality, subsuming
     the hand-proved eager/lazy switch lemmas (#465's engine becomes the operational semantics
     of a logic-level device). Clutch's §7 unsoundness counterexamples transfer as the test
     suite: the same examples must be *unprovable* here.
  3. *Approxis-shaped credits*: only after `11`'s ledger stabilizes — the relational
     error-credit camera and the hop ledger must be one accounting object (see §2.2 table,
     last row); building both independently is the failure mode this bullet exists to prevent.

### 4.3 What the two tracks do *not* attempt

- No port of Iris invariants/fancy updates into PolyFun (upstairs stays elementary);
- no probabilistic cofree comonoid (the `02` §3.3 caveat stands — S2 works over `evalDist`,
  never over M-equality of probabilistic branching);
- no commitment to completing iris-bluebell's `sorry` backlog — S2a/S2b consume its
  *definitions*; its unproved general rules are cited as intended-semantics, and only the lemmas
  our pilots need get proved (in the bridge repo if the fork is unresponsive);
- no unification of Loom, displays, and BI into one logic. Three surfaces, bridge theorems, per
  decision D3 — now with the §1 identifications as the reason bridges exist at all.

## 5. Integration levers (order)

| Step | Repo | Deliverable |
|---|---|---|
| 1 | VCVio | frame-independence transfer theorem over `runExp` (§1.1; feeds S2c and `05` R-5.3) |
| 2 | bridge repo | S1a frame camera + one ghost-state proof about the shared-RO cache |
| 3 | PolyFun | S1b behavior COFE (finite-projection `dist`), no iris dependency |
| 4 | bridge repo | S2a `wp`-transformer constructor from indexed VCVio programs; derived `wp_bind`/`wp_query` |
| 5 | VCVio | S2b `SPMF` conditioning lemma pack + lifting→`CouplingPost` bridge |
| 6 | bridge repo | S2c OTP + secret-sharing independence pilots |
| 7 | bridge repo | S2d.1 spec resource + adequacy bridge to `CouplingPost` (R-10.5) |
| 8 | bridge repo | S2d.2 seed tapes over `SeededOracle` + erasure theorem; Clutch-§7 negative tests |
| 9 | bridge repo | R-10.6 probe: one `C`-modality rule via ghost agreement over `SPMF` |

## 6. Rent tests

- **R-10.1**: OTP privacy proved in the independence style at length ≤ the current
  coupling-style proof, with the statement strengthened (independence, not just distribution
  equality).
- **R-10.2**: the frame-independence transfer theorem exists and is consumed by both R-10.1 and
  a `StateSeparating` lemma (deleting at least one hand-rolled independence argument).
- **R-10.3**: Bluebell `wp` instantiated with VCVio-backed semantics; `wp_bind` derived, not
  axiomatized; at least one end-to-end `wp` proof of a two-program relational fact that
  discharges to `CouplingPost`.
- **R-10.4**: one Löb-style proof over the behavior COFE replaces one `M.bisim` argument at
  comparable or smaller size.
- **R-10.5**: the spec-resource adequacy bridge exists (`specRes` refinement ⟹ `CouplingPost`),
  and one existing coupling proof is re-done as ghost moves — including at least one step where
  run-ahead or a seed-tape presampling does something the aligned-step `rvcgen` style cannot
  (an *asynchronous* coupling), so the layer demonstrates new capability, not re-packaging. The
  eager/lazy switch lemmas of #465 follow from the single erasure theorem.
- **R-10.6** (probe, allowed to fail): one Bluebell `C`-modality rule (a conditioning
  introduction or merge rule) derived over `SPMF` from an `Agree`-style ghost witness encoding.
  Success upgrades §2.3(3) from hypothesis to design; failure is recorded there with the
  obstruction.
- **Kill criteria**: if mathlib measure-theory friction (Bluebell's `ProbabilitySpace (α → V)`
  with `AEMeasurable` plumbing) makes S2a cost more than the `SPMF`-level reformulation, rebuild
  the S2 layer directly over `SPMF` in VCVio and demote the iris-bluebell bridge to
  documentation (the *logic* is what pays rent, not the fork). If R-10.4 shows Löb is just
  `M.bisim` with extra ceremony, drop S1b and keep the COFE as a remark in `02`. If the frame
  camera duplicates `OwnershipFrame` at equal cost with an extra dependency, record the
  comparison in `05` and stop S1 at the writeup.

## 7. Risks and honest column

- **Two moving dependencies.** iris-lean is mid-refactor (setoid→type port); iris-bluebell is a
  research fork on its own toolchain with `sorry`-grade rules. Everything lands in a bridge repo
  with pinned revisions; VCVio core acquires no iris dependency this cycle.
- **The Rocq family is years ahead.** Clutch/Eris/Tachis/Foxtrot have mature models, tactics,
  and case studies. The honest claim for S1/S2 is not novelty of the logic — it is (a) the
  frame-independence transfer theorem as the formal join between SSP state separation and
  probabilistic independence, which none of the Rocq line states (their languages have no package
  algebra), and (b) unification with the polyfun substrate (displays, behaviors) that a
  language-specific logic cannot see.
- **Bluebell's `C` modality is measure-theoretically heavy** (conditioning on null events,
  almost-everywhere plumbing). The `SPMF` (discrete) setting avoids the worst of it — VCVio's
  distributions are countably supported — so S2b should be stated over `SPMF` first and only
  generalized if a consumer demands continuous distributions.
- **Ghost-coupling soundness is subtle, and the literature says so out loud.** Clutch §7
  exhibits counterexamples where slightly-too-liberal presampling rules break soundness, and
  its adequacy/erasure proof (not the surface logic) is where the difficulty lives; Approxis's
  credit-quantified logical relation is another layer of hard metatheory. S2d budgets
  accordingly: adequacy bridges first, surface rules second, and the Rocq artifacts are the
  reference implementations to diff against, not just citations.
- **Scope honesty:** nothing in this direction advances UC composition, forking, or the quantum
  question; it is a proof-ergonomics and relational-vocabulary direction — though S2d gives it
  a second face: the ghost-coupling layer is *shared infrastructure* with `11`'s ledger (one
  accounting object) and with `03`'s deferred-sampling engine (one erasure theorem). Its paper
  value is as a section of paper 2 (the coalgebraic-adversary paper's "program logics over the
  substrate" story), not a standalone.
