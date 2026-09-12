# 04 — Direction 3: Displayed Structure as the Intrinsic Program Logic

**Claim.** Aberlé's merged display series (#74–#75, #84–#88, and #91–#98: `Display`, displayed
handlers, responder coalgebras and presentations, displayed parallel) is a *second* program logic for
VCVio — intrinsic and proof-relevant where Loom is extrinsic and semantic. Its immediate cash
value in VCVio is (a) instrumentation (`QueryTracking`) re-derived as decorations/displays with
transport for free, and (b) relational reasoning re-founded: a coupling of two oracle programs is
a displayed program over their lockstep parallel composite, whose *joint* evidence component is
exactly the shape of a pRHL judgment. Loom stays the user-facing surface (decision D3); displays
are the invariant-carrying layer underneath, connected by bridge theorems per carrier.

## 1. The two logics, and why both

| | Loom (today) | Displayed (G-series) |
|---|---|---|
| style | extrinsic: `wp`/triples computed over a finished program | intrinsic: evidence carried at each node |
| carrier | `MAlgOrdered` / `MAlgRelOrdered` over `Prop`/`ℝ≥0∞` | `Display P` (Type-valued, proof-relevant) over positions/directions |
| invariants | pre/post at boundaries | per-node, preserved by displayed responder coalgebras |
| transport | per-handler lemmas (`HandlerSpecs`, `SimulateQ` rules) | one theorem: displayed handlers compose along wiring (Abe26 Thm 5.3) |
| relational | `CouplingPost` (coupling existence over `evalDist`) | joint display over `P ∥ Q`'s `.both` branch — evidence "need not factor into unary pieces" |
| user surface | `vcgen`/`rvcgen`, EasyCrypt vocabulary | none yet (and none planned this cycle) |

The bet is *not* that displays replace Loom — SMT-adjacent extrinsic reasoning is why proofs are
short. The bet is that the places where VCVio currently pays a **per-wrapper, per-handler lemma
tax** are exactly the places where displayed transport is one theorem.

## 2. Current state (precise)

- VCVio instrumentation: `QueryTracking/` (counting, logging, caching, random-oracle state) with
  hand-kept lemma families; `Examples/CommitmentScheme/Hiding/LoggingBounds/*` re-proves logging
  bounds per context; query-bound side conditions threaded through `CryptoFoundations` games.
- VCVio relational: `CouplingPost` = coupling-existence; quantitative `ℝ≥0∞` carrier default;
  qualitative carrier `scoped` because Loom's `outParam` discipline permits one visible carrier
  (`Relational/Loom/Qualitative.lean` — a hard constraint on bridge design).
- PolyFun merged: `FreeM` **displayed free machinery already on main** (`Free/Displayed`,
  `Displayed/Decoration`, displayed cursors) — decorations exist and are consumed by the
  Interaction layer, not by VCVio.
- PolyFun merged (G-series): `Display` over polynomials with fiberwise morphisms (g6a),
  `PresentationHom` — witness-preserving simulation maps between responder presentations (g6b),
  displayed handlers + Sigma variant, `Wiring.lean` (Thm 3.1 eval-wiring; Thm 5.3 local handler
  composition), parallel displays with genuinely relational joint components (g6c), displayed
  lockstep execution (g6d), displayed responder parallel coherence (g6e–g6g), and bridges (g6h).

## 3. Design

### 3.1 Instrumentation as decoration (the cheap, high-confidence half)

Target: one wrapper first — **query counting**. Steps:

1. PolyFun (likely already sufficient on main): a decoration/display `CountD` over any `p`
   assigning ℕ-evidence per node; its preservation by handler lifts = instance of displayed
   handler transport.
2. VCVio: `countingOracle` re-derived: `countingOracle = forget (displayedLift CountD)`, with the
   existing `simp` lemma surface re-exported (`@[simp]` lemmas restated as corollaries — the rent
   test demands *no lost surface*, measured by the test files still elaborating).
3. Then logging (transcript display: per-node evidence = the `(i, t, u)` triple, fold = `QueryLog`),
   then the random-oracle cache (dependent display: evidence = cache table + freshness invariant —
   this is the first *genuinely dependent* payoff: cache-consistency lemmas in
   `QueryTracking/RandomOracle` become one preserved invariant).
4. Query bounds in games: `IsQueryBound`-style side conditions restated as "the program lifts
   along the bounded display" — an intrinsic certificate consumed by asymptotic layers.

### 3.2 Relational judgments as joint displays (the deep half)

The mathematical observation: a probabilistic coupling proof has three parts — a pairing of the
two programs' steps, per-pair relational evidence, and a lockstep discipline saying when steps
pair. Aberlé's parallel display provides exactly this typology: `Display.parallelSumComponents S T U`
with `U` over `P ⊗ Q` genuinely joint. So:

```lean
-- sketch: a relational display judgment on programs
def RelDisplayed (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (U : Display (spec₁.toPFunctor ⊗ spec₂.toPFunctor)) (post : α → β → Prop) : Type _ :=
  DisplayedLift U post (FreeM.parallel oa ob)   -- evidence over the lockstep composite
```

Bridge theorems (one per Loom carrier, respecting the `outParam` scoping):

- **soundness**: `RelDisplayed oa ob U post → CouplingPost oa ob post` when `U`'s joint evidence
  refines a coupling kernel per node (the constructive content: the display *is* the coupling,
  node by node — this should be near-definitional for the qualitative carrier);
- **quantitative**: joint evidence carrying per-node error mass folds to the `ℝ≥0∞` carrier
  (eRHL-style bound aggregation) — stated, attempted, and allowed to fail this cycle (fluid).

What lockstep buys concretely: today `CouplingPost` proofs pick a coupling of whole
distributions; the displayed form builds it by synchronized induction, which is precisely what
`rvcgen` does operationally — so the medium-term prize is **`rvcgen` soundness against the
displayed semantics**, giving the tactic a carrier-independent justification. That is a paper-2
level deliverable, kept fluid.

The known boundary (from `aberle-parallel.md`, must be respected in the design): lockstep
`FreeM.parallel` is not Kleisli-bifunctorial — interpreting one side can change synchronization.
Consequence: `RelDisplayed` composes sequentially along *synchronized* binds only; the bridge
lemma pack states congruence rules for exactly the compositions that hold (mirroring how pRHL's
seq rule demands aligned intermediate assertions — the counterexample is why that alignment is
not optional).

### 3.3 Presentation homomorphisms = witness-preserving simulations

g6b's `PresentationHom` maps give simulations that preserve dependent witnesses. VCVio consumer:
`SimSemantics` correctness statements ("this handler stack implements that spec preserving I")
become responder presentations and witness-preserving homomorphisms; the routing lemmas of #451
(simulateq routing) are candidates for
re-derivation. Kept as an opportunistic third track — pursued only where a routing proof is
already painful.

## 4. Integration levers (order)

| Step | Repo | Deliverable |
|---|---|---|
| 1 | VCVio | counting as decoration over merged displayed-free machinery (R-4.1) — needs no G-series |
| 2 | PolyFun | use merged g6a–g6h; add the Kleisli-instance lemma pack for displayed handlers |
| 3 | VCVio | logging + RO-cache displays; LoggingBounds example re-derivation (R-4.2) |
| 4 | VCVio | `RelDisplayed` + qualitative soundness bridge (R-4.3) |
| 5 | VCVio | SimpleTwoServerPIR privacy or OTP as displayed relational pilot (R-4.4) |

## 5. Rent tests

- **R-4.1**: counting wrapper derived from a display; all existing counting `simp` consumers
  still elaborate; net lemma count in `QueryTracking` decreases or holds with transport lemmas
  now imported, not local.
- **R-4.2**: one `LoggingBounds` file loses its bespoke per-context logging lemmas.
- **R-4.3**: `RelDisplayed → CouplingPost` proved for the qualitative carrier without touching
  the ambient-instance discipline (no third live carrier).
- **R-4.4**: one existing coupling proof re-done displayed, comparable length, strictly more
  informative statement (the coupling object is constructed, not just asserted to exist).
- **Kill criteria**: if (R-4.1) forces re-proving the whole `simp` surface by hand, decorations
  are vocabulary here — halt 3.1 after counting and record why. If the qualitative bridge needs
  choice-style extraction from `CouplingPost`'s existential to go the *useful* direction, keep
  displays as a proof *producer* (soundness only) and never claim completeness.

## 6. Risks and honest column

- The G-series is merged through #98; step 2 pins a `main` revision containing that API. Slices
  are sized so step 1 remains independent of responder-presentation machinery.
- Proof-relevant evidence can bloat elaboration (Type-valued displays over every node); the
  1500-line/file and lint gates on PolyFun will surface this early. If display-heavy files are
  slow, restrict displays to instrumentation boundaries rather than whole programs.
- EasyCrypt-honesty: pRHL with SMT remains shorter for flat games. The claim defended here is
  narrower: *transport* (instrumentation, handler stacks, wiring) is where intrinsic structure
  wins; flat coupling proofs may stay Loom-only forever, and that is fine.
