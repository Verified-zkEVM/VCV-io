# 02 — Direction 1: The Behavior Model of `OpenTheory`

**Claim.** Define a second concrete model of `OpenTheory` whose objects are *behaviors* — cofree
mates of processes — instead of process presentations. Coherence laws that the process model
satisfies only up to `OpenProcessActivationEquiv` become honest `Eq` by finality, the model climbs
the lawfulness ladder to (at least) `IsTraced` and plausibly `HasPlugWireFactor`, and the UC
composition theorems (`Emulates.par_compose`, `wire_compose`, `plug_compose`) apply for the first
time to a model with runnable content. This is the keystone direction: `03`, `05`, and `06` all
consume the behavior carrier.

## 1. Why now

This direction was impossible until this month. It needs exactly the three results PolyFun merged
in #65/#67/#68:

- `Cofree/Universal`: the cofree polynomial comonoid's universal property — a lens from any
  comonoid's carrier extends uniquely into the cofree comonoid;
- `Dynamical/CofreeMate`: a machine's behavior *is* its mate, with
  `DynSystem.cofreeMate_comp_projectionN` tying the mate to every finite run at once;
- `Cofree/FiniteProjection` (Prop 8.49): behavior determined by its finite projections.

Together these say: **the quotient that the process model pays for lemma-by-lemma (activation
equivalence) can be taken once, structurally, by mapping into the final object.** Two processes
are activation-equivalent exactly when suitable mates agree; downstream of the mate, equality is
`Eq` in a Mathlib `M`-type and `simp`/`rfl`-grade reasoning applies. This is also the design
lesson the ledger already extracted from CryptHOL/Constructive Crypto ("state-hidden equations are
much more concise") and the ArkLib ground rule ("behavior is the unique extensional relation
carrier; no quotients") — this doc is that rule executed on the UC layer.

## 2. Current state (precise)

- `OpenTheory` composition theorems (`Emulates.lean`) are proved at `HasPlugWireFactor` strength;
  the docstring itself notes the process model "instantiates only `IsLawful`" and that its
  coherence holds "up to `OpenProcessActivationEquiv`, not strict equality".
- The existing partial remedy, `plug_compose_of_observes_plug_comm`, must be acknowledged and is
  insufficient: it restores only the plug leg (not `par_compose`/`wire_compose`), demands a
  per-model `plug`-commutation observation, and its own docstring warns that a scheduler-only
  structural relation does not qualify. The behavior model subsumes it: with strict coherence,
  the `hcomm` hypothesis is discharged by `rfl`-grade lemmas once, and all three composition
  theorems apply. (Cheap intermediate milestone, usable before G-2c: instantiate
  `plug_compose_of_observes_plug_comm` at the behavior model's mate-equality observation — this
  gives a *plug-composition* pilot after G-2a only.)
- The process model (`OpenProcessModel.lean`) proves the up-to-equivalence versions by explicit
  step-relation matches (e.g. `openTheory_par_assoc_activation_equiv` with a hand-supplied
  state-triple relation) — exactly the per-theorem cost this direction deletes.
- VCVio's `Computational.lean`/`Standard.lean` quantify over an abstract `T : OpenTheory` and so
  inherit the gap: `UCSecure` statements about the process model cannot invoke the composition
  theorems.

## 3. Design

### 3.1 The carrier

For a boundary `Δ`, a *behavior at `Δ`* is an element of the final coalgebra of the step
polynomial that `OpenProcess` structures already induce (the same polynomial the Concurrent layer
uses to make processes dynamical systems). Concretely, in PolyFun terms:

```lean
-- PolyFun side (crypto-free), sketch:
def BehaviorObj (m) (Party) (Δ : PortBoundary) : Type _ :=
  M (stepPoly m Party Δ)          -- or CofreeP carrier at the step polynomial

def OpenProcess.behavior : OpenProcess m Party Δ → BehaviorObj m Party Δ
  -- the cofree mate of the process's step coalgebra (M.corec / CofreeMate)
```

The model:

```lean
def behaviorTheory (Party) (m) (sched) : OpenTheory where
  Obj Δ := BehaviorObj m Party Δ
  map φ := reindex along φ  (functorial on the final coalgebra)
  par   := behavior-level interleaving product (image of processes' par under behavior)
  wire  := behavior-level internalization
  plug  := closure to a closed-behavior object
```

with the defining constraint — **the mate is a homomorphism of theories**:

```lean
theorem behavior_par  : (W₁.par W₂).behavior = W₁.behavior ⋈par W₂.behavior
theorem behavior_wire : …
theorem behavior_plug : …
```

There are two construction strategies; the doc fixes the order of attack:

1. **Quotient-free (preferred):** define `par`/`wire`/`plug` directly on behaviors by
   `M.corec` over pairs of behaviors (the scheduler-interleaved step of two final coalgebras),
   then prove the process-level operations are mapped to them by `behavior`. Coherence laws are
   proved by the finality/uniqueness principle (`M.bisim` collapsing to `Eq`), which is exactly
   the proof style `CofreeMate` already set up. No setoid appears anywhere.
2. **Fallback:** if a direct corecursive `wire` proves too dependent-transport-heavy, define
   `BehaviorObj` as the image of `OpenProcess.behavior` and transport operations; this reduces
   coherence to `ActivationEquiv → mate-equality` (one theorem) plus the existing up-to lemmas.
   Acceptable only as a stepping stone: the end state must not quantify over presentations.

### 3.2 How high up the ladder

- `IsLawful`, `IsMonoidal`: expected by finality — associator/braiding on behaviors are
  corecursive isos whose defining squares are unique-morphism arguments. **Gate G-2a.**
- `IsTraced`: wire-associativity and superposition; same technique, more transport. **Gate G-2b.**
- `IsCompactClosed`/`HasPlugWireFactor`: needs `idWire Δ : Obj (swap Δ ⊗ Δ)` — the behavior of
  the relay/dummy process — and the zig-zag laws. The relay's behavior is a corecursively defined
  copy-cat; zig-zag is precisely the copy-cat argument from game semantics, which finality should
  make an `Eq`. This is the riskiest law (see §6); if it lands, the *entire* Emulates theorem
  suite applies verbatim. **Gate G-2c.**
- The scheduler is a parameter throughout: `behaviorTheory` is indexed by the same
  `schedulerSampler` as the process model, and `05` later refines "one global sampler" into a
  discipline parameter. Do not prematurely generalize here.

### 3.3 The probabilistic layer (VCVio side)

Behaviors upstairs are still `m`-parametric. VCVio instantiates `m := ProbComp`/`OracleComp` and
supplies the observation:

- `Semantics` (`Computational.lean`) gets a second constructor `Semantics.ofBehavior` running a
  *closed behavior* to `SPMF Result`. Key theorem — the semantic quotient is coarser:
  `W₁.behavior = W₂.behavior → sem.evalDist (close W₁) = sem.evalDist (close W₂)`.
  This is the formal version of "structural equality upstairs, distributional equality
  downstairs", and it is the only new probabilistic content this direction needs.
- **Distributional behavior is a second, coarser mate.** Probabilistic bisimilarity is *not*
  `M`-equality of `m`-branching behaviors (that distinguishes sampling order). Where a proof needs
  invariance under distribution-preserving reshuffling, it must pass through `evalDist` — i.e.
  the Kleisli-category mate, whose home is `Responder.equivStateHandler` + `tvDist`. The ledger's
  D3 note (CryptHOL's determinization functor as the design source for monad-weighted trace
  equivalence, which Spivak–Niu does *not* supply) applies verbatim; do not promise a
  probabilistic cofree comonoid.

### 3.4 Emulates/UCSecure over the behavior model

With G-2c, `Standard.lean`'s vocabulary specializes: `Protocol`/`Functionality`/`Adversary` become
behaviors, `EXEC π A Z` is a closed behavior, and:

- `Emulates` at `Observation.eq` becomes *perfect security as mate equality* — new, free notion;
- `ObservedCompEmulates` keeps its fixed-ε non-transitive form, unchanged;
- the composition theorems apply to concrete statements. The pilot theorem (rent test R-2.3) is a
  UC-style statement for OneTimePad or the commitment functionality whose proof uses
  `Emulates.wire_compose` on behaviors and *never mentions* `OpenProcessActivationEquiv`.

## 4. Integration levers (what to touch, in order)

| Step | Repo | Deliverable |
|---|---|---|
| 1 | PolyFun | `BehaviorObj` + `behavior` mate for `OpenProcess`; `behavior_par/wire/plug` homomorphism theorems |
| 2 | PolyFun | `behaviorTheory : OpenTheory` at `IsMonoidal` (G-2a), then `IsTraced` (G-2b) |
| 3 | PolyFun | copy-cat `idWire` + zig-zag → `HasPlugWireFactor` (G-2c) |
| 4 | VCVio | `Semantics.ofBehavior`; `behavior_eq → evalDist_eq`; port `Standard.lean` statements |
| 5 | VCVio | pilot end-to-end UC statement through composition theorems (R-2.3) |
| 6 | both | reconcile with k-l-examples `Implements`/`IsSimulation`/`RunLimit` (merge or re-derive as mate-facts; `08` gate G-0b) |

## 5. Rent tests

- **R-2.1**: count of `OpenProcessActivationEquiv` lemmas in the proof-term closure of the pilot
  UC statement = 0 (vs. every current process-model coherence use).
- **R-2.2**: `behaviorTheory` instantiates a ladder tier ≥ `IsTraced` with no `sorry`, no setoid,
  no `Quotient`.
- **R-2.3**: one concrete `Emulates.wire_compose` application at a probabilistic instance.
- **Kill criterion**: if after the G-2b gate the corecursive `wire` still requires more transport
  lemmas than the process model has activation lemmas (measured bluntly in lines), stop at the
  fallback construction and re-scope G-2c as research.

## 6. Risks and honest column

- **Zig-zag is genuinely hard.** Copy-cat identities in game-semantic settings are famously
  fiddly; finality helps only if the wiring corecursion is set up so both sides are corecursive
  images of the *same* coalgebra. Budget the g6h wiring bridges (#98) as prerequisite reading —
  they build exactly the reconstruction bridges this needs.
- **Universe pairs.** `Comonoid.Hom` currently fixes one universe pair (ledger "known risks");
  `behaviorTheory` should stay at the ambient `PortBoundary` universes and not attempt spanning.
- **`◃`-associator transport** contaminates any bicomodule-flavored restatement; this doc's model
  deliberately does *not* wait for D1 bicomodules. Bicomodules later *explain* the model
  (`06` §4); they are not on its critical path.
- **Honesty about content**: the behavior model does not add cryptographic power — every theorem
  it enables is "morally true" today. What it buys is that UC composition becomes *usable*, and
  proofs about wired systems stop being O(wiring-size) transport arguments. If Table-4-style line
  counts do not visibly improve on the pilot, say so in the paper-3 draft.
