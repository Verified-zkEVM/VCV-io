# VCVio × PolyFun Integration Design Suite (v1)

**Date:** 2026-07-22. **Status:** normative architecture, pre-implementation.
**Provenance:** a source-level audit of VCVio `main` (`a5f474fd`) and PolyFun `main`
(`f887c096`, through #99), including the now-merged PolyFun trains #66, #71–#72, #76–#83,
#88, and #91–#98, plus the PolyFun reading-note suite
(`docs/reading/` — `vcv-connection.md`, `composition-unification.md`, `roadmap.md`,
`aberle-parallel.md`, `pattern-runs-on-matter.md`, `coalgebra-related-work.md`), and the VCVio
paper (ePrint 2026/899). This suite is the companion, on the VCVio side, to PolyFun's own reading
ledger: the ledger records what each *Poly* construction buys; this suite is the **normative plan
for spending it** — including on the parts of VCVio (UC, scheduling, unbounded participants) the
ledger only gestures at as "Phase D".

## The design in one paragraph

VCVio becomes the probabilistic/cryptographic **instance** of one structural story told entirely in
PolyFun: programs are elements of free monads, implementations are behaviors (cofree-comonoid
elements, i.e. mates of machines), running an adversary against an implementation is the
pattern-runs-on-matter module action, packages and functionalities are one- and two-boundary
bicomodules over protocol comonoids, program logics are displayed structure over programs, and the
UC composition theorem is functoriality of the behavior assignment. The standing split is
**structural upstairs, distributional downstairs**: PolyFun proves equalities of behaviors and
lenses; VCVio's only residues are SPMF/`evalDist`/`tvDist` reasoning, computability, and
scheme-specific algebra. Every abstraction in this suite carries a falsifiable rent test naming the
existing hand-rolled construction it deletes or the theorem it newly makes provable; abstractions
that fail their rent test are dropped, not defended.

## Documents

| Doc | Contents | Stability |
|---|---|---|
| [`00-end-state.md`](00-end-state.md) | The ambition: compositional verified cryptography over one substrate; papers 2 and 3 | directional |
| [`01-substrate-inventory.md`](01-substrate-inventory.md) | Precise current state of both libraries, the disconnection points, merge-train constraints | **normative** (as audit) |
| [`02-behavior-model.md`](02-behavior-model.md) | Direction 1: the behavior-quotiented `OpenTheory` model via cofree mates; strict UC coherence | **normative** |
| [`03-pattern-adversary-ssp.md`](03-pattern-adversary-ssp.md) | Direction 2: pattern-runs-on-matter as the experiment engine; SSP as one-boundary case | **normative** |
| [`04-displayed-program-logic.md`](04-displayed-program-logic.md) | Direction 3: intrinsic displayed verification; QueryTracking as decoration; relational = joint display | normative core, fluid periphery |
| [`05-scheduling-and-ownership.md`](05-scheduling-and-ownership.md) | Direction 4: `∥`, schedulers as interleaving policies, SSP typing as the race-freedom discipline | normative interfaces, research internals |
| [`06-unbounded-participants.md`](06-unbounded-participants.md) | Direction 5: indexed polynomials, mode-dependent comonoids, spawning as reindexing, composition = functoriality | research (paper-3 core) |
| [`07-references.md`](07-references.md) | Annotated bibliography, including papers to acquire into paper-note | operational |
| [`08-roadmap.md`](08-roadmap.md) | Phases, tracks, gates, rent tests, risks, kill criteria | fluid by design |
| [`08a-phase1-pr-plan.md`](08a-phase1-pr-plan.md) | Exact Phase 0/1 PR slices with files, declarations, gates | operational |
| [`09-verification-ledger.md`](09-verification-ledger.md) | Every named anchor, verified location, merge status; correction history | **normative** (as fact base) |
| [`10-separation-logic.md`](10-separation-logic.md) | Direction 6: Iris/Bluebell over the substrate — three identifications (frames = resource PCMs, BI = joint displays, step-indexing = finite projections); zoom-in on the full Iris feature set (higher-order ghost state, camera catalogue as crypto bookkeeping, couplings as ghost state à la Clutch/Approxis, tapes = seed stores); tracks S1/S2 incl. the S2d ghost-coupling layer | normative core, fluid periphery |
| [`11-protocol-track.md`](11-protocol-track.md) | Direction 7: CryptoVerif's hop discipline, IPDL's equations, Owl's types; `game_hop` engine; signed-DH → TLS ladder | normative core, fluid periphery |
| [`12-quantum.md`](12-quantum.md) | Direction 8: boundary–carrier split, transfer certificates, QROM via compressed-oracle-as-dilated-mate, comb carrier | research (normative interface core) |

Reading order for a new contributor (or agent): 00 → 01 → 02 → 03 → 04 → 05 → 06 → 08 → 08a, with
07 and 09 as lookup. Docs 02 and 03 are the implementation front line; 04 runs in parallel; 05 and
06 are staged behind them. Docs 10–12 (added 2026-07-20) extend the suite outward — separation
logic, the protocol track, and quantum — and are read after their dependencies: 10 after 04/05,
11 after 02/03, 12 after 11 (its Q1 certificates ride the hop engine). An implementation session
takes its slice from 08a and greps its anchors from 09 before writing code. A verification review
round (declaration names, file paths, tier claims checked against both trees) was completed
2026-07-20 and the post-merge API/status cutover was re-audited 2026-07-22; corrections are
logged in 09.

## Resolved decisions (log)

- **D1 — Behaviors are the extensional carrier; the quotient is taken by finality, never by
  setoids.** Two systems are "the same" when their cofree mates are equal (`Eq` in the M-type).
  This is the same ground rule the ArkLib design suite already fixed ("behavior is the unique
  extensional relation carrier; no quotients") — the two suites must not diverge on this.
  Distributional equality (`evalDist`/`tvDist`) is a *second*, downstream relation, never conflated
  with behavioral equality. See `02`.
- **D2 — SSP and UC are one layer at different boundary arities.** A package is an open system
  with one wired boundary; the SSP reduction lemma and the UC composition theorem are the same
  module-law + simulation-invariance argument. The `StateSeparating/` and `Interaction/UC/` trees
  converge on shared PolyFun carriers rather than evolving separately. See `03`, `05`.
- **D3 — Two program logics, one substrate, explicit bridges.** Loom (extrinsic, predicate
  transformers) remains the user-facing proof surface; displayed structure (intrinsic, Aberlé) is
  the invariant-carrying layer underneath instrumentation and couplings. Neither replaces the
  other; the bridges are theorems, not aspirations, and each bridge has a rent test. See `04`.
- **D4 — Scheduling is a named discipline, not an ambient convention.** The failure of parallel
  interchange (`PolyFunTest` counterexample) is treated as a *feature*: every UC statement that
  depends on activation order names its scheduling discipline as a hypothesis. See `05`.
- **D5 — Probability stays downstairs.** PolyFun remains crypto-free. Anything requiring SPMF,
  ωCPO, `tvDist`, negligibility, or TM running time lives in VCVio. Behavior-level statements are
  proved in PolyFun and *instantiated* here. (Carried over from the ledger's load-bearing honesty
  note; restated because every direction in this suite touches the boundary.)
- **D6 — No new formalization starts without its rent test written down.** The rent-test idiom
  from PolyFun `roadmap.md` §"Is the abstraction paying rent?" is mandatory for every ticket in
  `08`.
- **D7 — Boundaries are adversary-model-neutral.** An `OracleSpec`/polynomial boundary is shared
  by classical and quantum strategy carriers; games are written against boundaries, never against
  a strategy carrier's internals (no transcripts, lazy sampling, or rewinding in game
  definitions). The classical instance of any parametric game must be a definitional match for
  the existing statement (zero-breakage gate). See `12`.
- **D8 — Cryptographic assumptions are registry objects.** One uniform bundle format (packages +
  interface + query bounds + explicit advantage function) for every registered assumption, with a
  `QuantumSound`-certificate slot from day one. Hop proofs apply registry entries; they do not
  restate assumptions inline. See `11`, `12` §6.
- **D9 — Separation logic enters through bridge theorems only.** Iris/Bluebell layers live in
  bridge repos with pinned revisions; VCVio core acquires no iris dependency, no third ambient
  Loom carrier appears, and every separation-logic proof discharges into existing carriers
  (`CouplingPost`, `Advantage`) via named bridges. Extends D3. See `10`.

## Ground rules carried forward

1. The three-library dependency direction is fixed: PolyFun ← VCVio ← ArkLib, acyclic, released as
   a train. This suite must stay consistent with the ArkLib design suite where they touch
   (behaviors as carrier, PolyFun ownership of structural algebra, VCVio ownership of worlds).
2. Operational machinery never outruns theorem support. A model of `OpenTheory` that satisfies
   only `IsLawful` is an admission, not an endpoint; docs must state which lawfulness tier each
   model honestly reaches.
3. Security definitions never silently weaken; quantifier order (∀A ∃S ∀Z vs ∃S ∀A ∀Z), the
   observation relation, and the scheduling discipline are part of a notion's name.
4. Existing PolyFun/VCVio semantics are extended, not shadowed. If a direction needs a construction
   PolyFun lacks, it becomes a PolyFun ticket (crypto-free) plus a VCVio consumer PR — never a
   VCVio-private copy of structural theory.
5. The honest column travels with every claim: where the abstraction is only vocabulary, where line
   counts currently lose, and where a competitor's approach is simpler, we say so in the doc.
