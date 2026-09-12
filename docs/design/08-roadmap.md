# 08 — Roadmap: Phases, Slices, Gates, Risks

Fluid by design. Every ticket is pre-split (PolyFun structural half / VCVio probabilistic half),
names its rent test from docs 02–06, and starts from the then-current default branches — this
branch is documentation provenance, **not an implementation base** (same rule as ArkLib's suite).

## Phase 0 — unblocking (before any direction lands)

- **G-0a Merge-train hygiene — passed 2026-07-22.** Pattern PRs #71/#72, the G-series (#88 and
  #91–#98; #89 was superseded), the issue-32 chain #76–#83, and dependent-chain PR #66 are on
  PolyFun `main`. Each VCVio slice now pins the minimal merged PolyFun revision it needs.
- **G-0b k-l-examples reconciliation.** `WireK`, `RunLimit`, `Coinductive/Machine`
  (`Implements`/`IsSimulation`) exist off-main. Decide per artifact: merge, re-derive as
  mate-facts (preferred for `Implements`/`IsSimulation`, per `02`), or retire. Blocking for
  `02` step 6 and the ledger's A1 payoff.
- **G-0c Acquisitions.** `07` §B items 1–7 into paper-note.

## Phase 1 — the two normative directions in parallel

**Track A (= `02`, behavior model):** A1 mate + homomorphism theorems → A2 `behaviorTheory` at
`IsMonoidal` (gate G-2a) → **A2.5 plug-composition pilot via `plug_compose_of_observes_plug_comm`
at mate-equality** (cheap early milestone; also an early-warning probe for G-2c) → A3 `IsTraced`
(G-2b; consumes `05` step-1 interchange lemmas) → A4 copy-cat + `HasPlugWireFactor` (G-2c) → A5
VCVio `Semantics.ofBehavior` + pilot UC statement (R-2.1–R-2.3). Exact slices: `08a`.

**Track B (= `03`, experiment engine):** B1 Kleisli lemma pack for `runThrough` → B2 `runExp` +
identification (kill-checked here) → B3 derive link-assoc + simulation-invariance, delete twins
(R-3.1) → B4 hybrid combinator + PRFTagReader port (R-3.2) → B5 fork-as-pattern-surgery pass
(R-3.3).

Tracks A and B are independent until A5/B3 (both touch `Semantics`/`evalDist` bridges); the shared
lemma is `behavior_eq → evalDist_eq`, built once in whichever lands first.

## Phase 2 — displayed logic and disciplines

**Track C (= `04`):** C1 counting decoration on merged machinery (R-4.1; no G-series needed —
can start in Phase 1 if agent bandwidth allows) → C2 logging + RO-cache displays (R-4.2) →
C3 `RelDisplayed` + qualitative bridge (R-4.3) → C4 relational pilot (R-4.4).

**Track D (= `05`):** D1 `SchedulingDiscipline` + interchange packs (feeds G-2b — schedule
early) → D2 discipline-indexing naming pass (R-5.1) → D3 `OwnershipFrame` + race-free wiring
(R-5.2) → D4 shared-RO frame (R-5.3, joint with C2's cache display) → D5 dummy-adversary
derivation (joint with A4).

## Phase 2b — outward tracks (directions 6–8, added 2026-07-20)

Three tracks from docs 10–12. None blocks Phases 1–3; each names its entry condition.

**Track S (= `10`, separation logic):** S0 frame-independence transfer theorem over `runExp`
(entry: B3; feeds R-5.3) → S1a frame camera in a bridge repo (entry: none; runs the `05`
kill-criterion comparison; build against `iProp`/`gFunctors`, not bare `UPred` — `10` §2.1) →
S1b behavior COFE via finite projections (entry: A1) → S2a Bluebell `wp` gets VCVio-backed
programs (bridge repo) → S2b `SPMF` conditioning + lifting→`CouplingPost` bridge → S2c
OTP/secret-sharing independence pilots (R-10.1–R-10.4) → **S2d ghost-coupling layer** (`10`
§2.3/§4.2): spec resource + adequacy bridge (R-10.5), seed tapes over `SeededOracle` + erasure
theorem with Clutch-§7 negative tests, `C`-modality-as-ghost-agreement probe (R-10.6); S2d.3
(relational error credits) waits on Track P's ledger format so the two stay one accounting
object.

**Track P (= `11`, protocol track):** P0 assumption registry + bundle format (entry: B3; **must
carry the `QuantumSound` certificate slot from day one** — D8) → P1 `game_hop` matching +
advantage ledger → P2 `guess`/`up_to_bad` combinators → P3 replay pilot + IPDL parity case
(entry for parity case: G-2a) → P4 epoch combinator + signed-DH FS pilot (R-11.1–R-11.4) →
(next cycle) TLS-handshake-core skeleton.

**Track Q (= `12`, quantum):** Q0 parametric `StrategyModel` + zero-breakage gate R-12.1
(entry: none, pure interface work — but co-designed with P0's bundle format) → Q1 `QuantumSound`
certificates + axiom-tagged transfer theorem; PQ schemes get stated quantum theorems (entry: P1)
→ Q2 QROM interface pack (O2H et al.) + FO restatement (R-12.2, R-12.4) → Q3 comb carrier +
compressed oracle (research; separate resourcing decision, not scheduled by this roadmap).

Ordering pressure across tracks: P0/Q0 are the cheapest high-leverage steps (formats and
interfaces others must conform to) and should land before P1/Q1 consumers exist; S0 is a single
theorem with three consumers (`05`, `10`, `03`'s honest column) and can go anytime after B3.

## Phase 3 — the paper-3 pilot (= `06`)

E1 `Topology` + reindexing-spawn carrier → E2 one-session `F_com` on the behavior model (reuses
A5 artifact) → E3 `!F_com` + emulation statement (R-6.1) → E4 composition instance π⟹!π via
functoriality squares (R-6.2) → E5 one corruption event (R-6.3). Entry condition: G-2b passed and
R-3.1 landed (the pilot must not hand-roll what Phases 1–2 made derivable).

## Parallelization guidance for agent sessions

- One session per lettered step; sessions must read `01` + their direction doc before coding.
- PolyFun halves obey PolyFun's AGENTS rules (crypto-free, DAG, no-sorry, update-lib); VCVio
  halves keep `ofFreeM`/`toFreeM` as the only unfolding seam.
- Any step's kill criterion firing ⇒ stop the track, write the post-mortem *into the direction
  doc* (honest column), and re-plan here; do not route around a failed rent test.

## Standing risks (cross-references)

| Risk | Where handled |
|---|---|
| copy-cat/zig-zag hardness | `02` §6; fallback construction §3.1.2 |
| probabilistic behavior ≠ M-equality (sampling order) | `02` §3.3; D3 ledger note (determinization) |
| `Ξ`-vs-`simulateQ` failure plumbing (`OptionT`) | `03` §5 kill criterion |
| display elaboration cost | `04` §6 |
| interchange lemmas resist proof | `05` §4 (shared fate with G-2b) |
| universe collisions in indexed carriers | `06` §4 kill criterion |
| upstream API churn after the merged train | pin a reviewed PolyFun `main` revision per slice |
| line-count honesty (paper Table 4) | every direction's honest column; report in paper drafts |
| iris-lean/iris-bluebell drift; mathlib measure-theory friction | `10` §7; bridge repos with pinned revisions |
| matching brittleness in `game_hop` | `11` §5 kill criterion (regress to marked hops) |
| parametric-game elaboration noise breaking R-12.1 | `12` §5 kill criterion (EasyPQC mirror fallback) |
| axiom-grade quantum middle years | `12` §6; axiom tagging + `#print axioms` checks |

## Success snapshot (what "done" looks like, one line each)

Pilot UC statement through `wire_compose` with zero activation-equivalence lemmas; SSP reduction
lemma derived; one hybrid chain deglued; counting/logging/cache as displays; one displayed
relational proof; discipline-named async theorems; race-free-wiring theorem; `!F_com` with
spawning as reindexing. Those eight artifacts *are* the paper-2/paper-3 evidence base. From the
outward tracks: OTP privacy as an independence proof; a hop-engine replay of an existing hybrid;
signed-DH with a forward-secrecy statement; ML-KEM with classical and quantum security statements
sharing one game definition.
