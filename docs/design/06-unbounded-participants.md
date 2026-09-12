# 06 — Direction 5: Unbounded Participants, Spawning, and Composition as Functoriality

**Status: research (paper-3 core).** This doc fixes the *shape* of the solution and its pilot so
implementation agents don't improvise ITM emulation; internals are expected to move.

**Claim.** Dynamic party/session topology — the genuinely hard part of UC — needs no new
execution machinery. Three existing PolyFun devices compose into it: (1) **indexed polynomial
functors** (`IPFunctor I`, indexed free monads, indexed M-types from g4) with the index = the
directory of live machines; (2) **spawning as reindexing** along index inclusions (cartesian, so
probability-preserving by the existing Thm-5.1 discipline); (3) **mode-dependent comonoids** whose
positions record current topology, so "corruption/creation changes the interface" is a structure
map, not an event side-effect. The UC composition theorem then has its conceptual home:
**functoriality of the behavior assignment** — behavior of the composite = composite of behaviors
— which is also the organizing principle of Myers' categorical systems theory (`07`).

## 1. What the literature actually needs (requirements, from the UC corpus)

From Canetti 2000/067 and the IITM/iUC line (`07` acquisitions):

- **R1 unbounded, dynamically created machines** — but every *reachable* execution touches
  finitely many; the infinite object is a colimit of finite stages.
- **R2 session/party identifiers** routing messages to instances (SID/PID discipline).
- **R3 corruption changing interfaces mid-execution** (VCVio already has the *data*:
  `CorruptionModel`, `MomentaryCorruption` alphabets).
- **R4 adversarial scheduling** — `05`'s disciplines; not re-solved here.
- **R5 polynomial-time accounting across spawns** — explicitly *deferred* (paper-1's TM boundary
  stands; only query/spawn counting is theorem-grade, via `04` decorations).

IITM's insight (why we follow it rather than raw 2000/067): a *directory-disciplined* model with a
uniform "!"-replication is enough for all standard applications and vastly more tractable. Our
translation: replication = indexed families; the directory = the index.

## 2. Design

### 2.1 The index is the topology

```lean
-- PolyFun side, sketch. Directory = finitely-supported set of live machine ids with roles.
structure Topology (Sid Pid Role) where
  live : Finset (Sid × Pid)
  role : ∀ i ∈ live, Role          -- includes corruption status: Role := Honest | Corrupt …

-- The protocol's interface at a given topology: an indexed polynomial
def protoIface : Topology Sid Pid Role → PFunctor := …
-- The whole protocol: an object over the index category of topologies
-- (IPFunctor with I := Topology, or a functor Topology-inclusions → Poly)
```

Key structural decisions:

- **Topologies form a poset** (inclusion + role-refinement, e.g. Honest ≤ Corrupt if corruption
  is monotone this cycle; momentary corruption drops monotonicity later). Executions live over
  *directed paths* in this poset.
- **Spawning is reindexing along an inclusion** `T ↪ T'`: a cartesian lens
  `protoIface T' ⇆ protoIface T ⊗ (new instance's iface)`. Cartesianness is the payoff: the
  existing probability-preservation discipline (paper Thm 5.1 / ledger A3) applies to spawns with
  zero new probabilistic argument. The g3/g5 displayed-reindexing machinery is the tool.
- **An unbounded execution is a colimit over finite stages**: behaviors at growing topologies
  with restriction maps (the `Display`-restriction-along-cursors machinery, #58, is the
  finite-stage restriction). R1 is met without any infinite carrier beyond the M-types we have.

### 2.2 Mode-dependence: topology as comonoid state

The comonoid whose positions are topologies and whose directions are the events that change them
(spawn, corrupt, close-session) is the *protocol category* of the execution. A running system is
then a machine over the composite "topology-comonoid ◃ per-topology interface" — Spivak-style
mode-dependent wiring. This is where Phase D pays: D4 (`IPFunctor I J` ↔ bicomodules over
discrete comonoids) says the §2.1 presentation and this comonoid presentation are the same thing,
and D1–D3 make environments/hybrids-over-changing-topology bicomodule composites. **Dependency
honesty:** §2.1 does *not* wait for Phase D — indexed pfunctors and reindexing are merged/g-series
material; the comonoid packaging upgrades the presentation when D lands.

### 2.3 Corruption as interface morphism

`CorruptionModel`/`MomentaryCorruption` currently act through env-event alphabets (runtime
side-effects). End state: a corruption event is a topology step `T → T'` whose reindexing lens
*swaps the party's interface* (honest iface ⇆ adversary-controlled iface). Leakage
(`Leakage.lean`) is the cartesian part (answers restricted); control transfer is the vertical
part — the vertical–cartesian factorization (merged, A3) is literally the honest/malicious
decomposition. This single reading unifies three files that today don't reference each other.

### 2.4 Composition as functoriality

The paper-3 statement shape:

```text
behavior : (systems over topology-indexed interfaces, wiring) ⟶ (behaviors, wired behaviors)
UC composition = behavior is functorial + Emulates is a congruence for the image operations
```

`02` proves the fixed-topology case (behavior_par/wire/plug homomorphism theorems). This
direction extends the functoriality *along topology change*: behavior-restriction commutes with
reindexing (a naturality square per spawn/corruption event). Myers' doubly-indexed-functor
packaging is the citation and sanity check; we formalize only the squares our pilot consumes.

## 3. Pilot (the gate that keeps this honest)

**A multi-session commitment functionality `!F_com`** — the canonical UC example needing R1–R3:

1. one-session `F_com` as a behavior-model functionality (`02` pilot artifact reused);
2. `!F_com`: sessions spawned on first use, indexed by SID (§2.1); emulation statement for a
   protocol using it stated over the topology poset;
3. the composition theorem instance: `π` emulates `F` (single session) ⟹ `!π` emulates `!F` —
   the *joint-state-free* JUC-lite statement, scheduling discipline named per `05`, proved
   through the functoriality squares;
4. one corruption event exercised (static corruption first; momentary is a stretch goal).

## 4. Rent tests

- **R-6.1**: `!F_com` stated with spawning as reindexing; no bespoke "machine array" carrier; the
  statement mentions no execution-model plumbing beyond topology steps.
- **R-6.2**: the `π ⟹ !π` composition instance proved from behavior-functoriality squares, not
  by induction over runtime traces.
- **R-6.3**: corruption = one reindexing lens; `CorruptionModel`'s alphabet semantics re-derived
  from it for the pilot's case.
- **Kill criteria**: if topology-indexed behaviors force universe gymnastics that leak into user
  statements (the `AsyncRuntime` universe-0 constraint colliding with indexed carriers), freeze
  §2.1 at a fixed `Sid Pid : Type` universe-0 instance — that covers all UC practice — and
  record the general case as blocked on PolyFun's universe-pair work. If R-6.2's squares each
  need bespoke transport, the functoriality framing is not yet paying; ship the pilot with direct
  proofs and keep the framing as documentation until D-phase machinery matures.

## 5. Honest column

- This is the direction where "payoff is a paper, not deleted lines" (ledger Phase D verbatim).
  Nothing in the current example library gets shorter; what's bought is that `!F_com`-class
  statements become *possible* without an EasyUC-scale (≈18k-line) routing investment.
- The JUC/GUC layer (joint state, global functionalities) is deliberately excluded from the pilot;
  `05`'s shared-RO frame is the preparatory work, and joint-state UC is its own future doc.
- Momentary/adaptive corruption breaks poset monotonicity; the design anticipates it (paths, not
  filtered colimits) but the pilot does not prove it.
- No claim of Canetti-model bit-fidelity: we target IITM-style adequacy. If a reviewer demands
  2000/067-exactness, that is a translation appendix, not an architecture change.
