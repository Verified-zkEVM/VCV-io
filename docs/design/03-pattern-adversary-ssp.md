# 03 — Direction 2: Pattern-Runs-on-Matter as the Experiment Engine; SSP as Its One-Boundary Case

**Claim.** The Libkind–Spivak module action `Ξ : Free(P) ⊗ Cofree(Q) → Free(P ⊗ Q)` (merged in
PolyFun #71/#72) is the canonical semantics of "run the adversary against the implementation": the
adversary is the pattern, the package/functionality/oracle is the matter, and the module laws are
the composition laws of security experiments. VCVio's state-separating layer is the one-boundary
instance: `QueryImpl.Stateful` *is* a responder (matter), package composition *is* responder
composition, and the SSP reduction lemma factors as generic `runAgainst`-invariance under
simulation plus a `tvDist` layer. This collapses D2 of the decision log ("SSP and UC are one
layer") into implementable steps.

## 1. The dictionary, written down once

| Crypto notion (VCVio today) | Pattern/matter notion (PolyFun) | Where |
|---|---|---|
| adversary `A : OracleComp E α` | pattern `FreeM p α` | definitional (`OracleComp = FreeM`) |
| package / handler `QueryImpl.Stateful I E σ` | responder / Kleisli–Mealy machine over `E ⊸ ·` in `StateT σ (OracleComp I)` | `Responder.equivStateHandler` |
| ideal functionality / lazy oracle | matter: element of `Cofree(Q)` (state-free behavior) | mate of the responder |
| `simulateQ h A` then `evalDist` | `Ξ`-run `runAgainst`/`runThrough`, then SPMF layer | #71/#72 + VCVio |
| package composition `linkWith` | responder composition / module associativity `runOn_assoc` | #71 |
| SSP reduction lemma (repackaging invariance) | `runBehaviorThrough_eq_of_isSimulation` | #72 |
| hybrid argument step | run-canonicity (`Run_n` canonicity, Prop 7.20d) + module laws | merged B-phase |
| game with transcript instrumentation | decorated matter (see `04`) | G-series |
| rewinding / forking | cursor/occurrence-fork algebra acting on the pattern | merged, consumed by #488 |

Two entries deserve emphasis because they are *theorems already proved upstream, unclaimed
downstream*:

- `runOn_assoc`/`runOn_unit` (Thm 3.4 of Libkind–Spivak) — "running A against (M₁ linked to M₂)"
  equals "running (A run against M₁) against M₂". That *is* the associativity of package linking
  that SSP frameworks prove by hand (SSProve's link-assoc; CryptHOL's inline lemmas).
- `runBehaviorThrough_eq_of_isSimulation` — if matter M₁ simulates matter M₂, running any pattern
  through them yields equal behaviors. That *is* the structural core of "indistinguishable
  packages compose": the probabilistic content left over is only that the SPMF-semantics of equal
  behaviors are equal (Direction 1's `behavior_eq → evalDist_eq`) or ε-close under a coupling.

## 2. Current state (precise)

- VCVio: `QueryImpl.Stateful` with state frames over vwb `PFunctor.Lens.State` lenses +
  `separated` non-interference (`SimSemantics/StateT/StateSeparating.lean`); advantage/hybrid/
  identical-until-bad layers over it (`StateSeparating/`); everything proved directly against
  `simulateQ`-algebra.
- PolyFun: #71/#72 are merged on `main`. `FreeP.runOn`/`xi` + `runOn_eq_xi`
  (categorical = operational),
  naturality, module laws, `runThrough` (any lawful monadic handler target), `runAgainst`
  (internal-hom evaluation — the same `eval` wiring as `DynSystem.game`), substitution
  compatibility, dynamical presentation `DynSystem.runPattern` agreeing with existing finite game
  semantics, and the invariance theorems. Merged prerequisites: internal hom + eval/curry (A1),
  substitution monoids, cofree work.
- The ledger's A1 payoff note ("`WireK.wireKStep` and UC `processSemanticsOracle` become the same
  wiring along eval") is the two-boundary echo of the same unification; `WireK` is on
  k-l-examples, so its unification lands with the `08` G-0b reconciliation.

## 3. Design

### 3.1 The spine: `runExp`

One VCVio definition becomes the single point through which experiments are run:

```lean
/-- Run adversary `A` against stateful matter `h` from `s₀`: THE experiment.
Existing API (verified on main): `Stateful.run h s₀ A = (simulateQ h A).run' s₀ : OracleComp I α`
(final state discarded; the state-retaining sibling threads `.run`). -/
def runExp (h : QueryImpl.Stateful I E σ) (s₀ : σ) (A : OracleComp E α) :
    OracleComp I α :=
  -- today: h.run s₀ A
  -- end state: the Kleisli instance of FreeP.runThrough at h's responder
```

with the normative theorem `runExp_eq_runThrough` identifying today's definition with the
`Ξ`-instance. Nothing downstream changes syntactically; what changes is which lemmas are *derived*:

- `runExp` associativity over `linkWith` ← `runOn_assoc` (delete the bespoke proof);
- `runExp` invariance under handler simulation ← `runBehaviorThrough_eq_of_isSimulation` +
  `evalDist` bridge (this replaces the core of the SSP reduction lemma);
- hybrid-step glue ← run-canonicity, stated once for the chain-of-hybrids combinator.

### 3.2 Packages as bicomodule-shaped data (naming, not new math)

Rename/annotate rather than rebuild: a `QueryImpl.Stateful I E σ` is an *open implementation with
import boundary `I`, export boundary `E`, and state `σ`*. Composition `linkWith` is boundary
composition; `parSumWith` is tensor. Document the correspondence to bicomodules (Phase D1) in the
module docstring **but do not block on D1**: the SSP layer needs only the module action and
simulation invariance, all available on `main`. When D1 lands, the docstring claim upgrades to the
theorem `Stateful I E σ` ↔ bicomodule between the state comonoids; that upgrade is `06`'s business.

### 3.3 What deletes, what stays

Deletes (target list for the refactor PR, to be checked against actual proof terms):

- bespoke associativity/unit lemmas for `linkWith` chains in `StateSeparating/Hybrid.lean`;
- per-example repackaging lemmas in PRFTagReader's `MultipleToHybrid`/`PRFReductions` glue;
- the structural half of `IdenticalUntilBad`'s setup (the bad-event split stays probabilistic).

Stays (honest column):

- everything `tvDist`/coupling-shaped: `Advantage`, `DistEquiv`, `IndistAt`, the bad-event
  probability bound — this *is* the VCVio-side residue and it is most of the crypto content;
- `CellRef` and state frames: they are the ownership discipline (`05` consumes them);
- eager/lazy sampling switches (deferred-sampling engine, #465): orthogonal machinery; connect,
  don't subsume.

### 3.4 Forking and rewinding as pattern surgery

#488 already derives replay forking from PolyFun contexts. The remaining step is doctrinal: state
in `CryptoFoundations` that *rewinding = running the same matter under a forked pattern* — the
cursor/occurrence-fork algebra acts on the pattern side of `Ξ` and never touches matter. This
gives the Fischlin and Fiat–Shamir developments a shared vocabulary ("fork at cursor c, replay
against unchanged matter") and should shrink `SeededFork`'s bespoke surface. Pilot: restate one
Bellare–Neven fork step through `runExp` + cursor-fork and diff the proof.

## 4. Integration levers (order)

| Step | Repo | Deliverable |
|---|---|---|
| 1 | PolyFun | build on merged #71/#72; add the Kleisli-target instance lemma pack for `runThrough` at `StateT σ (OracleComp I)` |
| 2 | VCVio | `runExp` + `runExp_eq_runThrough`; no consumer changes |
| 3 | VCVio | derive link-assoc + simulation-invariance; delete bespoke twins (R-3.1) |
| 4 | VCVio | hybrid combinator over run-canonicity; port one PRFTagReader hybrid (R-3.2) |
| 5 | VCVio | fork-as-pattern-surgery doctrinal pass over Fischlin/FiatShamir (R-3.3) |

## 5. Rent tests

- **R-3.1**: the SSP reduction lemma's proof shrinks to (generic invariance) + (`evalDist`
  bridge); net negative diff in `StateSeparating/`.
- **R-3.2**: one PRFTagReader hybrid chain loses its per-hybrid glue lemmas; hybrid count in the
  statement unchanged (no weakening).
- **R-3.3**: one forking-lemma step stated as cursor surgery on the pattern with matter untouched;
  `SeededFork` surface shrinks or its docstring explains why not.
- **Kill criterion**: if `runExp_eq_runThrough` needs more than a small compatibility layer
  (because `simulateQ`'s `OptionT`/failure plumbing resists the `Ξ` shape), keep `runExp` as
  today's definition and take only the invariance theorems as *lemmas about* it; drop the
  identification claim from docs. (The ledger's honesty note — "`OracleComp = FreeM` is standard
  effects; the Poly language adds expository value" — is the fallback position, and it is still a
  net win because the invariance theorems remain.)

## 6. Risks and honest column

- `Ξ` is stated for `Cofree` matter; stateful handlers are Kleisli coalgebras, so the VCVio
  instance runs through `runThrough` (monadic-handler schema), not through literal `Cofree`. The
  distributional-mate caveat of `02` §3.3 applies: sampling-order-insensitive statements need
  `evalDist`, not behavior equality.
- SSProve/CryptHOL comparison honesty: SSProve's package algebra is mature and its link-assoc is
  cheap there because everything terminates by construction; our win is the *combination* with
  coinduction, dependent interfaces, and no-axiom forking — not the algebra in isolation. Say so
  wherever this direction is written up.
