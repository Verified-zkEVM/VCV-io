# 12 — Direction 8: Quantum Adversaries, QROM, and the Boundary–Carrier Split

**Status: research with a normative interface core.** §2's boundary–carrier split and its
zero-breakage gate are normative for this cycle; §3's stages Q2–Q3 fix the shape of a multi-year
program and are expected to move.

**Claim.** "Programs as oracle computations" genuinely fails for quantum adversaries — a quantum
algorithm querying in superposition is not a tree that branches on answers — but the failure is
confined to one layer. An `OracleSpec` (= a polynomial: positions are queries, directions are
answers) is an *interface*, and interfaces are adversary-model-neutral. What varies is the
**carrier of strategies over the boundary**: `FreeM p` is the *classical* strategy carrier; the
quantum strategy carrier over the same boundary is a quantum comb (Chiribella–D'Ariano–Perinotti)
over the boundary's dilated Hilbert interface. The correct generalization for VCVio is therefore
not "make `OracleComp` quantum" but a **boundary–carrier split**: schemes, games, and wiring are
written once against boundaries; security statements are indexed by the strategy carrier; and the
analysis paths (classical vs. quantum) diverge only below that line. The user-facing litmus test
this direction is graded against: *existing schemes and games stay definitionally unchanged, and
each post-quantum scheme acquires classical and quantum security statements that share one game
definition.* QROM enters as the quantum matter for the random-oracle boundary, with Zhandry's
compressed oracle as the quantum counterpart of the caching mate.

## 1. What breaks, what survives (the audit)

| Layer | Classical status | Quantum status |
|---|---|---|
| `OracleSpec ι = ι → Type` boundaries | interfaces | **survive unchanged** — a query type and answer type per index is exactly what gets dilated to registers |
| schemes / honest algorithms | `OracleComp` programs | **survive unchanged** — post-quantum schemes are classical algorithms; this is the litmus test's core demand |
| game structure (key sampling, wiring, win predicates, `SecExp` advantage layer) | `ProbComp`/`SPMF` | **survives** — advantages are probabilities of classical outcomes of a measurement at the end |
| adversary carrier | `FreeM` element (tree branching on answers) | **breaks** — superposition queries; no tree, no transcript |
| transcript/logging/counting (`QueryTracking` as data) | wrapper handlers | **breaks in general** — recording queries is measurement; no-cloning forbids a transparent log. Query *counting* survives (comb slot count); query *content* tracking does not |
| lazy sampling / RO cache | caching handler = the RO's mate | **breaks as stated; survives transformed** — compressed oracle = purified lazy sampling (superposed databases); the correct quantum object is a *dilation of the caching responder*, not its deletion |
| rewinding / cursor-fork algebra (#488) | pattern surgery on the tree | **breaks in general** — measurement destroys state; quantum rewinding is its own theory (Watrous; Unruh; CMSZ; Lai–Malavolta–Spooner in paper-note) and is *not* a cursor operation |
| identical-until-bad | bad-event coupling | **breaks** — no event happens "during" a superposed execution; the substitute is the O2H family |
| SSP package *shape* (interfaces + composition) | `QueryImpl.Stateful` | **shape survives** — packages with quantum implementations are channels between register interfaces; the wiring diagrams are the same diagrams |
| scheduling/ownership disciplines (`05`) | affine wiring, no contraction | **survive with new significance** — see §3.4: the no-contraction discipline is exactly the fragment compatible with no-cloning |

The break rows are not folklore: BDF+11 (the paper that defined the QROM) names exactly four
classical proof techniques that do not carry over offhand — **adaptive programmability,
extractability/preimage awareness, efficient simulation (on-the-fly lazy sampling), and
rewinding/partial consistency** — and additionally exhibits a *separation*: a (contrived)
two-party protocol secure in the classical ROM — even against quantum attackers with classical
oracle access — yet insecure in the QROM and under every concrete instantiation of the hash. So
"classical ROM theorem + PQ assumption" is
formally *not* a post-quantum security statement, which is the entire reason this direction
exists; VCVio currently cannot even state the distinction.

The table is the design: everything in rows marked "survives" must be *shared* between the two
analysis paths; everything marked "breaks" must live *below* the carrier index, never in a game
definition. A game definition that mentions transcripts, lazy sampling, or rewinding is at the
wrong level — this is a checkable doc-discipline for the existing library (and `GPVHashAndSign`,
which already cites BDF+11 in its docstring while proving a ROM theorem, is the first file the
discipline audits).

## 2. The unified interface (normative core)

### 2.1 Strategy models

```lean
-- VCVio side, sketch. The boundary stays an OracleSpec; the carrier is the index.
class StrategyModel (M : Type) where
  Strat  : {ι : Type} → OracleSpec ι → Type u → Type v   -- adversaries at boundary `spec`
  runWith : ∀ {ι} {spec : OracleSpec ι} {α},              -- execution against matter
    MatterFor M spec → Strat spec α → SPMF α
  queries : Strat spec α → ℕ                              -- resource accounting survives
  -- composition laws: wiring a strategy through a boundary morphism, sequential composition
```

with two intended instances:

- **`Classical`**: `Strat spec α := OracleComp spec α`, `MatterFor` = a `QueryImpl` bundle +
  initial state, `runWith` = `simulateQ` then `evalDist`. **Gate (zero-breakage):** at this
  instance every parametric game must be *definitionally* today's game — checked by the existing
  examples elaborating unchanged against the parametric statements. If this gate needs more than
  unfolding lemmas, the design is wrong (kill criterion §6).
- **`Quantum`**: `Strat spec α` = a comb over the dilated boundary (§3.3); opaque this cycle
  (Stage Q1 treats it as an interface with axioms; Stage Q3 constructs it).

Security notions then split cleanly: for a scheme `S` and game `G S : ∀ M [StrategyModel M], …`,
classical security is `G S Classical`-hardness and quantum security is `G S Quantum`-hardness —
one game, two statements, which is precisely the litmus test. The `SecExp`/advantage layer needs
only `SPMF Bool` out of `runWith`, so it is carrier-generic already.

Precedent that this split is the right architecture, not an invention: post-quantum-sound
CryptoVerif (Blanchet–Jacomme, CSF 2024) had to do exactly this to its own system — the paper's
summary is that it "required an update of the whole semantics in order to define it for any
**black-box interactive attacker** and not just probabilistic Turing machines," after which
every game transformation was re-validated against that attacker class. Their semantics update
is our `StrategyModel`; their transformation re-validation is Q1 below.

### 2.2 What is deliberately *not* parametrized

Honest parties, functionalities, and reductions stay classical (`OracleComp`) this cycle —
which is also BDF+11's own modeling decision ("honest parties and the scheme's algorithms can
access O only via classical bit strings"); the litmus test's demand is the QROM's original
design point, not an extra constraint.
Parametrizing the *matter* side (quantum functionalities, quantum channels between parties) is a
real research direction (quantum UC) explicitly out of scope; the seam left for it is that
`MatterFor` is already a parameter of the class rather than fixed to `QueryImpl`.

## 3. The quantum carrier, staged

### 3.1 Stage Q1 — transfer certificates (no Hilbert spaces in Lean)

The pragmatic state of the art — EasyPQC (CCS 2021) and post-quantum-sound CryptoVerif
(Blanchet–Jacomme CSF 2024, both in paper-note) — does not build quantum semantics either: it
*audits classical proof steps for quantum soundness* and forbids the rest. Adopt exactly that,
made explicit in the hop discipline of `11`:

- each `game_hop` step (registry application, `guess`, statistical distance, algebraic rewrite,
  black-box reduction with same-boundary wiring) carries or lacks a **`QuantumSound`
  certificate**; the certified set is the EasyPQC/CV-PQ audited list, whose forbidden side is
  BDF+11's four named techniques (no adaptive programming, no extractability/preimage
  awareness, no on-the-fly lazy sampling, no rewinding) plus `up_to_bad` without an O2H
  replacement;
- the certificate idiom has a *pedigree older than the audit lists*: BDF+11's **history-free
  reductions** are exactly a certificate on a classical proof — a reduction that answers RO
  queries independently of the query history — with the meta-theorem "history-free classical
  security proof ⇒ quantum security," and GPV signatures are their flagship instance. So
  `QuantumSound` should be a *structured* type with (at least) constructors for
  `historyFree`-style whole-reduction certificates and per-hop step certificates, not a bare
  marker Prop;
- **transfer theorem (Q1 keystone, initially assumption-grade):** a hop chain all of whose steps
  are `QuantumSound`, from a game whose assumptions are stated at the `Quantum` instance,
  yields the `Quantum`-instance bound. Its Lean status is an explicitly `axiom`-tagged
  meta-theorem citation (BDF+11 Thms for the history-free constructor; EasyPQC/CV-PQ for the
  step lists) until Q3 gives it semantics — the suite's honesty rules require saying so in the
  statement's docstring, and the axiom is quarantined in one file so consumers are greppable.

Q1's payoff is real despite the axiom grade: the PQ schemes already in-tree (ML-KEM, ML-DSA,
SLH-DSA, Falcon) get *stated* quantum security theorems whose proofs are audits of existing hop
chains — the statements become library surface, the audit becomes doc-discipline, and the axiom
is a named debt with a repayment plan, which is strictly better than the current state (quantum
security not even statable).

### 3.2 Stage Q2 — the QROM lemma pack as interface

The QROM's working lemmas have *classical statements*: they bound advantages by query counts.
One-way-to-hiding (semi-classical O2H, Ambainis–Hamburg–Unruh), measure-and-reprogram,
compressed-oracle bounds (collision/preimage), small-range distributions — each is
`∀ A : Strat Quantum roSpec α, advantage-inequality(queries A, …)` with no quantum object in the
*statement*. AHU's own precision matters for the interface shapes: a *semi-classical oracle*
measures only whether the query lies in a forbidden set `S` (nothing else), it appears **only in
intermediate games** — final statements remain plain QROM — and the modern O2H bounds are
parametrized by query number `q` *and query depth* `d` (parallelism), support non-uniform oracle
distributions, multiple reprogrammed points, and joint input/oracle distributions, with
square-root-of-probability forms for guessing games. The Q2 interface therefore carries `(q, d)`
from day one and does not bake in uniformity of the oracle distribution. Stage Q2 states these
as interfaces over the parametric games (axiom-tagged like Q1, with literature citations
pinned), and re-derives one flagship result through them: the existing `FujisakiOkamoto`
development restated so its ROM theorem (today's) and QROM theorem (via the O2H interface) share
the game definitions. Comparison baselines, chosen with care because **the QROM-FO literature
has a live flaw**: the December 2021 revision of AHU carries a notice that its Appendix B FO
proof is broken (found by Maram) with "we do not know whether the theorem can be fixed" — so the
baselines are Zhandry's compressed-oracle FO proof (ePrint 2018/276, which also removes the
extra hash term earlier proofs needed) and Unruh's qrhl-tool FO verification (ePrint 2020/962),
the only mechanized QROM FO proof in existence, in a bespoke logic. Matching the *statement*
through interfaces while sharing the classical game with the classical proof would already be a
first — and the AHU flaw is the standing exhibit for why this literature deserves mechanization
at all.

### 3.3 Stage Q3 — combs as the honest carrier (research)

The actual quantum instance, for finite boundaries (`spec.Fintype` — all crypto uses finite
query/answer types):

- **dilation**: each index `i` with query/answer types `Q i`, `A i` gets registers
  `H_Q i ⊗ H_A i` (finite-dimensional); the standard oracle unitary for classical matter `f` is
  `U_f |q,a⟩ = |q, a ⊕ f q⟩`;
- **adversary**: a `q`-query strategy is a comb `U_0, slot, U_1, slot, …, U_q, measure` — the
  Chiribella–D'Ariano–Perinotti quantum comb over the dilated boundary (PRA 2009, in
  paper-note); `runWith` is comb contraction against the matter channel;
- **compressed oracle as the dilated mate**: Zhandry's construction (how-to-record-quantum-
  queries) breaks what his paper names the **recording barrier** — recording a query is a
  measurement the adversary can detect by uncomputing, so naive on-the-fly simulation is
  distinguishable from a true random oracle. The resolution's own slogan is the design cue:
  since the adversary is entangled with a uniform superposition of oracles and entanglement is
  symmetric, *the oracle may record what the adversary knows* — yielding "efficient on-the-fly
  simulation of random oracles, roughly analogous to the usual classical simulation" (the
  paper's abstract), i.e. purified lazy sampling with a superposed database register. In suite
  vocabulary: the classical RO's matter is the cofree mate of the caching responder
  (`03`/`04`); the QROM's matter is that responder's dilation, and the compressed-oracle
  invariants are `04`-style displayed invariants on the database register. This is the precise
  sense in which the substrate's *shape* survives: same responder, new base category. Payoff
  evidence that this is the right Q3 centerpiece: the technique's launch results include the
  first quantum indifferentiability proof for Merkle–Damgård — domain extension is exactly the
  hash-construction reasoning the VCVio/ArkLib stack (Merkle trees, BCS) will eventually need
  quantumly, and BDF+11-era techniques provably cannot do it (any indifferentiability simulator
  *must* record queries).
- **substrate**: fin-dim Hilbert spaces, unitaries, channels, measurement — mathlib's matrix
  analysis plus the growing Lean quantum-information layer (Lean-QuantumInfo, indexed in
  paper-note) are the candidate bases; a serious gap analysis is a Q3 entry task, not assumed
  solved.

Q3 discharges the Q1/Q2 axioms: the transfer theorem becomes a theorem about combs (black-box
steps commute with dilation), and O2H gets its proof (it is ~a page of operator algebra on
paper; the Lean cost is the substrate, not the argument).

### 3.4 The missing generalization, named precisely (PolyFun's stake)

Poly is cartesian: `Set`-valued positions/directions, diagonal freely available — and the
diagonal is exactly what no-cloning forbids. The quantum analogue of the free-monad/cofree-
comonoid/lens story is interpretation of the *same boundary signatures* in a symmetric monoidal
category **without contraction** (fin-dim Hilbert spaces / CPTP maps), where combs play the role
lenses/wiring play in `Set`. Two consequences, one immediate and one long-range:

- **immediate (doctrinal):** the `05` ownership/affine discipline — committed counterexample
  "no contraction in `evalParallel`," frames licensing wiring — is the fragment of substrate
  reasoning that is *quantum-compatible by construction*. Proofs disciplined to affine wiring
  are the ones with a chance to transfer; this is an independent, non-quantum reason `05` was
  right to make contraction a licensed exception rather than ambient. Cross-cite both ways.
- **long-range (research, not a ticket):** a PolyFun-adjacent theory of "polynomial boundaries
  interpreted in a monoidal category" (enriched/linear polynomial functors; the comb category as
  the quantum `Org`). **PolyFun itself stays `Set`-based and crypto-free this cycle** — no
  Hilbert spaces upstairs; the comb layer is VCVio-side (or a third library) with only the
  *boundary types* shared. Anything more is a paper-3-era conversation with the PolyFun roadmap,
  recorded here so it is not reinvented.

## 4. Out of scope (hard lines this cycle)

Quantum honest parties and quantum functionalities (quantum UC); QKD-style protocols;
superposition access to *protocol* messages (only oracle access is dilated); quantum proofs of
quantumness of the *reductions*; QRAM/quantum-memory cost models (the lattice-estimator papers in
paper-note cover the cryptanalytic side; none of it enters the framework); quantum rewinding
formalization (statable as Q2-style interfaces if a consumer appears; CMSZ-grade machinery is its
own multi-year project).

## 5. Rent tests

- **R-12.1 (zero breakage)**: IND-CPA and EUF-CMA restated parametrically; at `Classical` the
  statements are definitional matches for today's; every existing consumer example elaborates
  unchanged.
- **R-12.2 (litmus)**: one PQ scheme — ML-KEM via the FO development — carries classical and
  quantum security statements sharing one game definition; the quantum one is proved from Q1/Q2
  interfaces with its axiom-dependencies explicitly listed by a `#print axioms`-grade check.
- **R-12.3 (audit pays)**: one existing hop chain (`GPVHashAndSign` is the designated candidate
  — deliberately, because BDF+11 *proved GPV quantum-secure via a history-free reduction*, so
  the ground truth is known) is certified and pushed through the transfer theorem, ideally by
  establishing the `historyFree` certificate for the existing reduction rather than step-by-step
  auditing; any hop that fails is documented with its O2H-style replacement or with an honest
  "classical-only" verdict in the file.
- **R-12.4 (stretch)**: semi-classical O2H stated as a Q2 interface and consumed by one FO-QROM
  bound.
- **Kill criteria**: if R-12.1's zero-breakage gate fails (parametrization leaks typeclass or
  universe noise into user statements), invert the design: keep games classical-only, add a
  parallel quantum-game mirror plus per-scheme transfer lemmas (EasyPQC's actual architecture),
  and record in this doc why the unified interface was not achievable in Lean's elaboration
  discipline. If the Q1 certified-step list cannot be given non-vacuous membership criteria
  (i.e., auditors cannot decide what is `QuantumSound` without reading the meta-papers per
  case), Q1 regresses to documentation and Q2's interfaces become the only quantum surface.

## 6. Risks and honest column

- **Axiom-grade middle years.** Q1/Q2 rest on explicitly tagged meta-theorem citations. This is
  the same epistemic position EasyPQC and PQ-CryptoVerif occupy — stated here without
  euphemism: until Q3, VCVio's quantum theorems are *conditional on the audit literature*, and
  every such statement must say so mechanically (axiom tracking), not just in prose.
- **Nobody has solved this.** qrhl-tool is the deepest mechanized QROM work and lives in a
  bespoke logic with its own trust story; EasyPQC axiomatizes; CoqQ/Lean-QuantumInfo are
  general quantum-program/information layers without crypto games. If Q3 lands even for fixed
  finite boundaries with one O2H proof, that is a publishable first — which is also the honest
  warning about its cost.
- **The litmus test is satisfiable now precisely because it is an interface demand.** Defining
  games at the right level costs elaboration engineering (R-12.1), not quantum mathematics; the
  quantum *analysis* path matures behind it independently. This decoupling is the direction's
  entire bet; if the decoupling itself fails (kill criterion), the honest fallback is the
  EasyPQC mirror architecture, which loses elegance but none of the statements.
- **Interaction with `11`:** the hop-certificate audit (Q1) and the hop engine (`game_hop`)
  must be co-designed — a hop step's bundle format carries the certificate slot from day one,
  or retrofitting will touch every registry entry. This is a one-line requirement on `11`'s
  step-1 format, flagged there as well.
