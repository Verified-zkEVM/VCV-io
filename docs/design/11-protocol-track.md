# 11 — Direction 7: The Protocol Track — CryptoVerif's Hop Discipline, IPDL's Equations, Owl's Types

**Status: normative core (the CryptoVerif recast §1–§2, the `game_hop` layer §3.1, the pilot
ladder §3.4), fluid periphery (Owl-as-displays §3.3, automation depth).**

**Claim.** VCVio must be demonstrably good at what working cryptographers spend most of their
time on: protocols built from encryption, signatures, MACs, and key exchange — with multiple
sessions and key compromise — not only at "fringe" strengths like axiom-free forking. The three
mature systems to mine each contribute one missing layer, and each has a precise reading in the
substrate this suite already builds: **CryptoVerif** shows that game hops are *rewrites by
package-shaped indistinguishability assumptions, found by matching modulo structural laws* — and
PolyFun proves exactly those structural laws; **IPDL** shows that UC-shaped protocol proofs
become short when observational equivalence is a congruence for composition — which is the
behavior model (`02`) by construction; **Owl** shows that an information-flow type discipline
discharges the routine bulk of protocol security — and a type discipline over interaction
programs is displayed structure (`04`). The track's endpoint is a TLS-class handshake proof;
its this-cycle pilot is a signed-Diffie–Hellman key exchange with a corruption event, proved
through a reusable hop engine rather than bespoke hybrids.

## 1. What CryptoVerif actually is, in our vocabulary

Sources: Blanchet's foundational paper (ePrint 2005/401), the long formal-semantics version
(arXiv 2310.14658), manual v2.12, composition theorems for TLS 1.3 (CSF 2018), dynamic key
compromise (CSF 2024), post-quantum soundness (CSF 2024) — all in paper-note. Stripped of its
process-calculus syntax, the system is three components:

1. **An assumption library of package equivalences.** A cryptographic assumption is registered
   as `equiv` — an indistinguishability statement `L ≈_ε R` between two *oracle systems* with
   explicit query interfaces, replication bounds, and an advantage function ε(time, queries).
   IND-CPA, EUF-CMA, PRF, DDH/GapDH, ROM lemmas — all in one format. This is the SSP insight
   (assumptions are packages) predating SSP's name for it, and it maps verbatim onto `03`'s
   carrier: an `equiv` is a `DistEquiv`/`Emulates`-grade fact between two `QueryImpl.Stateful`
   bundles (or behaviors, post-`02`).

2. **A matching engine.** A "cryptographic transformation" locates an occurrence of `L` inside
   the current game — i.e., produces a factorization `G ≈ C[L]` with `C` a context built from
   the calculus's structural laws — and rewrites to `C[R]`, accumulating ε. The reduction *is*
   the context `C`. In substrate terms: factorization through `runExp`/`linkWith` composites,
   where legality of the factoring moves is exactly the module laws (`runOn_assoc`,
   run-canonicity) and simulation invariance that PolyFun proves generically (`03` §1). What
   CryptoVerif hard-codes as calculus metatheory, this suite has as named theorems.

3. **An advice loop (the actual automation).** When matching fails, the prover computes which
   *syntactic* transformations would make it succeed — `RemoveAssign` (inlining),
   `SArename` (splitting a variable by assignment site), `expand`/`Simplify` (normalization,
   equational pre-rewriting), `insert event` (bad-event introduction), `guess` (session
   guessing), plus global dependency analysis — applies them, and retries. User hints
   (interactive mode) name the assumption occurrence or the preparatory step. Probability
   bookkeeping is fully automatic throughout.

**The good parts to adopt:** the uniform assumption format; matching-modulo-structural-laws as
the definition of a hop; the advice loop's *shape* (hints name occurrences, the engine does
bookkeeping); automatic advantage accumulation; the CSF 2018 composition theorems for key
exchange (a protocol-level modularity result our UC layer should subsume, not re-prove); the
CSF 2024 dynamic-compromise treatment as the requirements list for adaptive corruption.

**The parts to leave out:** the non-foundational trust base (an OCaml prover whose soundness
lives in a paper — the entire reason to redo this in Lean); matching brittleness tied to one
concrete calculus (arrays + `find` as the state idiom, replication indices in scope threading);
no higher-order constructions; limited exotic-technique coverage (no rewinding/forking — exactly
where VCVio is already strong; the two strengths are complementary, which is the point).

## 2. IPDL and Owl, same exercise

**IPDL** (Morrisett–Shi–Sojakova–Fan–Gancher, POPL 2023; ePrint 2021/147 — author order
randomized in publication): a *channel-centric* calculus — the unit of composition is not a
party but a **write-once channel with an associated reaction** (a straight-line probabilistic
program that may read other channels once they fire); protocols are parallel compositions of
channel bindings; control flow lives at the level of data, not the calculus. The main judgment
is approximate observational equivalence `P ≈_δ Q` with the advantage δ tracked symbolically
through every rule, and UC-shaped statements are `real ≈_δ ideal ∥ Sim`. Deliberate
restrictions, from the paper: straight-line reactions with *statically bounded* loops (bounds
may be Coq-level parameters — number of parties, sessions, circuit size), static corruption
fixed a priori, message *scheduling entirely adversarial* (no activation order — messages fire
in any protocol-consistent order; contrast UC's sequential-activation token, and note this is
exactly a `05` scheduling-discipline choice made at the calculus level). Adversaries are
arbitrary PPT machines. Mechanized in Rocq; the artifact (`github.com/ipdl/ipdl`) makes the
proof-size claim concrete: their multi-use secure-network example is **195 lines including
definitions and proofs, vs. 12,203 lines they count for EasyUC's single-use analogue**
(key-exchange excluded on both sides); at repo HEAD the case-study directories measure OTP/PRF
257, secure channel + CPA 279, coin-flip-with-abort 472, DHKE 744, GMW 614, OT 2220 lines, over
a ~3.8k-line core. The reading: IPDL processes are open-system presentations, and its
equational theory is a hand-picked fragment of what `OpenTheory` + `Emulates`-congruence + the
module laws provide; IPDL works because equivalence is a congruence for its composition
operators *by construction of the logic* — which is precisely what the behavior model buys us
as theorems (`02` §3.4). Its restrictions (bounded loops, static corruption, no dynamic
topology) are boundaries `06` is built to pass. Adoption: not the calculus — the *proof-size
discipline*. Every hop in an IPDL proof is one equation; our hop engine should make VCVio
proofs read the same way. The artifact numbers above are the honest baseline for R-11.2.

**Owl** (Gancher–Gibson–Singh–Dharanikota–Parno, S&P 2023, ePrint 2023/473; OwlC follow-up,
USENIX Sec 2025, ePrint 2025/1092): security by an information-flow + refinement type system in
the computational model. The load-bearing ideas, from the paper: randomness (keys, nonces) is
declared through **names** with *name types* fixing the invariant each key must protect (e.g.
`enckey (Name(msg))` — key-cycle freedom by fiat); labels are conjunctions of atomic `[n]`s with
a flows-to lattice and an adversary label `adv`; **corruption is per-name and hierarchical**
(corrupting `psk` transitively corrupts everything derived from it), not per-party; the
`corr_case` construct *splits typechecking on whether a name is corrupt*, so honest-case
guarantees and corrupt-case degradation are both discharged in one pass; authenticity rides
refinement types over a `happened(...)` predicate; localities index parties (`Client⟨i⟩`) and
protocols carry **module types**, so subprotocols typecheck separately against abstract
interfaces and a Secure Transport module is verified without knowing which Key Exchange
implements it. Typing rules are proven sound **once and for all, on paper**, against arbitrary
PPT adversaries; the tool (Haskell + Z3; artifact `github.com/secure-foundations/owl`)
typechecks in seconds. Announced limitations: guarantees are *asymptotic only* (no concrete
bounds), corruption is *static*, flows are deliberately over-approximated. Case studies: 14,
including Needham–Schroeder(-Lowe), LAK/MW RFID protocols, and simplified SSH KE and Kerberos;
OwlC then compiles typed protocols to verified, interoperable, constant-time-hardened Rust
(WireGuard — a ~670-line Owl spec in the artifact — and HPKE) at industrial performance. The
reading: **an Owl-style label assignment is a display over the protocol's interaction
boundary** — labels decorate positions/directions, well-typedness is a displayed lift of the
protocol program, and the soundness theorem is a (one-per-lattice) bridge from the displayed
lift to a simulation statement. That makes Owl the third instance of `04`'s thesis (program
logics are displayed structure), alongside instrumentation and relational judgments. Two
differentiators to preserve, not erase, when borrowing: VCVio's registry format targets
*concrete* advantage functions where Owl is asymptotic-only, and `12`'s certificates need the
assumption format Owl deliberately hides from its users. Adoption is deliberately staged: this
cycle only a recast memo + toy (a typed one-message flow whose displayed lift discharges its
secrecy hop); a real typed front-end is a paper-sized project. OwlC's extraction story is
`Interop/`'s business (the hax/aeneas seam), noted and not planned here.

## 3. Design

### 3.1 The hop engine (`game_hop`)

One tactic-visible layer, three components, all consuming existing machinery:

1. **Assumption registry.** An attribute (working name `@[game_equiv]`) registering
   indistinguishability facts in a uniform bundle: the two packages (as `QueryImpl.Stateful`
   bundles or, post-`02`, behaviors), the query interface, the query-count parameters, and the
   advantage function as an explicit `ℝ≥0∞`-valued term. Existing `DistEquiv`/`Advantage` lemmas
   for IND-CPA/PRF/DDH-style assumptions are the initial population. Infrastructure precedent:
   the `@[vcspec]`/`@[wpStep]` discr-tree registries in `ProgramLogic` — same indexing machinery,
   different payload. **Format requirement from `12` (D8): the bundle carries a
   `QuantumSound`-certificate slot from day one** — retrofitting it later touches every entry.
2. **Occurrence matching, hint-first.** `game_hop ‹assumption› at ‹occurrence›` factors the
   current game through the named package occurrence: the tactic constructs `G ≈ C[L]` where the
   factoring steps are `runExp` associativity, run-canonicity, and simulation invariance (`03`'s
   derived lemma pack), then rewrites and emits the ε obligation. **Interactive-first is a design
   decision, not a fallback**: the user names the hop (as in CryptoVerif's interactive mode and
   in every EasyCrypt proof); the engine's job is the factorization bookkeeping and the
   advantage ledger. Search (CryptoVerif's advice loop) is a later, separable layer: a hint
   suggester that tries registered assumptions against the goal's discr-tree footprint —
   valuable, unproven, explicitly *not* load-bearing for the rent tests.
3. **The advantage ledger.** A hop-chain state accumulating ε terms and query-count side
   conditions (discharged against `QueryBound`/`04` decorations), producing at chain's end a
   single triangle-inequality bound in the existing `Advantage`/`Asymptotics` vocabulary. This
   deletes the per-example "sum the hybrids" arithmetic that every current example hand-rolls.
   **Design constraint from `10` §2.2/§2.3:** the ledger must stay isomorphic to a relational
   error-credit resource (Eris/Approxis `£ε` — Approxis's mechanized PRP/PRF switching and
   IND$-CPA proofs are exactly this ledger living inside a separation logic), so that `10`'s
   ghost-coupling layer and this tactic-level ledger remain two views of one accounting object.

Two named combinators complete the engine, both standard-technique gaps found by the CryptoVerif
comparison rather than new ideas:

- **`guess`** — the session/index-guessing lemma (`Adv ≤ n · Adv[guessed instance]`), stated
  once over `runExp` with the guess as a wrapper package. Consumers already latent: multi-session
  arguments in PRFTagReader, and every AKE pilot below.
- **`up_to_bad`** — the `insert event`/Shoup move: `IdenticalUntilBad` repackaged as a hop step
  emitting a bad-event probability obligation, so failure-event hops enter the same ledger
  instead of living in a separate idiom.

### 3.2 Corruption and compromise (the CSF 2024 requirements, mapped)

Forward secrecy and post-compromise security statements are corruption-*event* statements: the
adversary obtains a party's state mid-execution. The substrate already carries the data
(`MomentaryCorruption`, env alphabets, `05`/`06`'s corruption-as-reindexing end state). What the
protocol track adds is the *hop discipline* for it, mined from Blanchet CSF 2024: compromise
splits the proof into epochs (pre/post-compromise), `guess` selects the attacked session, and
assumptions apply only to keys whose secrecy survives the epoch analysis. Owl's `corr_case` is
the type-level precedent for exactly this move — case-split on corruption status with both
branches discharged — and its *per-name, hierarchical* corruption model (corrupt a key ⇒ all
keys derived from it) is the right granularity for the epoch analysis: what an epoch boundary
corrupts is a name-closure, not a party. Note the division of labor among the mined systems:
Owl is static-corruption-only, so the dynamic-compromise discipline comes from CryptoVerif
(whose CSF 2024 treatment handles keys compromised *during* execution) while the case-split
*mechanism* comes from Owl. Deliverables: an
epoch-splitting combinator over the async runtime's event stream (`05`'s discipline hypotheses
name when the split is sound), and one FS statement in the pilot (§3.4). Unbounded/adaptive
corruption *models* stay `06`'s business; this doc only consumes their fixed-topology,
finitely-many-events fragment.

### 3.3 Owl-as-displays memo (scoped)

One design memo + one toy this cycle: define a two-point label display (secret/adv) over a
one-message protocol boundary, show a well-typed program lifts, and prove the bridge "lift ⇒ the
message-secrecy hop is free" for that fragment. Success is measured by whether the memo's bridge
statement generalizes in an evident way (to key-indexed labels, Owl's `Name` discipline);
if it does, a typed front-end becomes a paper-2/paper-3-adjacent project with this memo as its
seed. No other Owl commitment this cycle.

### 3.4 The pilot ladder ("traditional cryptographer" milestones)

1. **P-1 (engine shakedown):** replay an existing multi-hybrid proof — ElGamal IND-CPA (or one
   PRFTagReader chain, coordinating with R-3.2 to avoid double-porting) — through `game_hop` +
   ledger. No new crypto; measures engine overhead against bespoke proofs.
2. **P-2 (IPDL parity):** one IPDL case study as an `Emulates`-congruence equational proof over
   the behavior model, against the artifact's own directory as the yardstick — cheapest first:
   the authenticated-to-secure channel (`Chan/`, 279 lines) or coin-flip-with-abort
   (`CoinFlip/`, 472 lines); OT (2,220 lines) only as a stretch.
3. **P-3 (the track's namesake):** signed Diffie–Hellman key exchange (SIGMA-lite): EUF-CMA +
   GapDH + PRF assumptions from the registry, `guess` over sessions, one static-corruption
   forward-secrecy statement via the epoch combinator. This is the "protocols cryptographers
   care about" demonstrator.
4. **P-4 (horizon, next cycle):** TLS-1.3-handshake-core skeleton following Blanchet CSF 2018's
   decomposition (their composition theorem shapes the module boundaries; our UC layer should
   discharge the composition step natively). Not scheduled; named so P-3's interfaces are built
   facing it.

## 4. Integration levers (order)

| Step | Repo | Deliverable |
|---|---|---|
| 1 | VCVio | assumption registry + bundle format; populate with IND-CPA/EUF-CMA/PRF/DDH from existing files |
| 2 | VCVio | `game_hop` occurrence matching over the `03` lemma pack; advantage ledger |
| 3 | VCVio | `guess` + `up_to_bad` combinators; retrofit one existing example each |
| 4 | VCVio | P-1 replay; P-2 IPDL parity case |
| 5 | VCVio | epoch combinator + P-3 signed-DH with FS statement |
| 6 | docs | Owl-as-displays memo + toy (joint with `04`) |

Dependency note: steps 1–3 need only `03`'s Track B (through B3); P-2 additionally wants `02`'s
G-2a. Nothing here waits on the G-series or Phase D.

## 5. Rent tests

- **R-11.1**: the P-1 replay has fewer manual proof steps than the bespoke original, and its
  final bound is produced by the ledger, not by hand-summed hybrids.
- **R-11.2**: the P-2 case study lands within 2× the corresponding IPDL artifact directory's
  line count (§2 table: 279 for the channel case, 472 for coin-flip), measured the same way —
  definitions + statements + proofs, core library excluded on both sides. Honest yardstick:
  they are a special-purpose calculus; we are a general framework — if we exceed 2×, the
  equational surface of the behavior model is not yet usable and that finding goes in `02`'s
  honest column.
- **R-11.3**: P-3 exists: a signed-DH security statement with at least one corruption event,
  whose proof contains no bespoke hybrid glue — every hop is a registry application, `guess`,
  `up_to_bad`, or an epoch split.
- **R-11.4**: the registry format survives contact with all of IND-CPA, EUF-CMA, and GapDH
  without per-assumption special cases (format uniformity is CryptoVerif's core lesson; losing
  it is failure even if individual proofs work).
- **Kill criteria**: if occurrence matching modulo monad/module laws proves too brittle even
  hint-first (factorizations requiring manual `conv`-style navigation), regress to *marked* hops
  (user rewrites, engine only runs the ledger) — still a win, recorded as such. If the ledger
  cannot beat hand-summed advantage arithmetic on P-1, the track stops at combinators
  (`guess`/`up_to_bad` pay for themselves regardless).

## 6. Risks and honest column

- **Automation honesty.** CryptoVerif's fully automatic mode rests on a decade of matching
  heuristics; nothing this cycle competes with that. The claim is different: *foundational* hop
  proofs at *interactive* cost comparable to EasyCrypt, with CryptoVerif's bookkeeping
  automated. Full advice-loop search is future work and might never pay in a dependently-typed
  setting.
- **The registry's ε-functions** (concrete-security advantage terms with query counts) will
  stress the `Asymptotics` layer's current shapes; some assumption statements may need
  restating. That is a feature (it forces the concrete-security surface to be uniform) but it is
  migration work not counted in the lever table.
- **IPDL comparison caveat**: IPDL's adversaries are arbitrary PPT, but its *protocols and
  simulators* are syntactically restricted (straight-line reactions, statically bounded loops,
  static corruption) and its scheduling is fully adversarial by fiat; our P-2 must state the
  exactly-matching theorem — same simulator class, same scheduling discipline (`05` vocabulary)
  — or name the quantifier difference (ground rule 3).
- **Owl comparison caveat**: Owl trades expressiveness for automation aggressively (no forking,
  no rewinding, restricted assumption forms). The memo must state which Owl case studies are
  *out* of the displayed fragment, not only which are in.
- **What this track does not claim**: no symbolic-model integration (ProVerif/Tamarin-style),
  no wire-format/implementation security (that is `Interop/`), no UC-vs-game-based unification
  beyond what `02`/`03` already provide — the track *uses* the unified layer; it does not extend
  it.
