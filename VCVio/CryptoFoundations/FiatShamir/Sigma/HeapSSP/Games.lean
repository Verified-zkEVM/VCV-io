/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Spec
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.HeapSSP.Composition

/-!
# Game packages for the HeapSSP Fiat-Shamir EUF-CMA proof

The four HeapSSP packages taking part in the EUF-CMA hop chain, with
heap-structured state:

* Each package carries a `Heap Ident` over its own cell directory, with
  identifier sets drawn from `Sigma/HeapSSP/Spec.lean`.
* The simulated game is *defined* as a link composition,
  `cmaSim := cmaToNma.link nma`, so the program-equivalence hop H4 is
  definitional: `cmaSim = cmaToNma.link nma` by `rfl`.
* `cmaReal` is a *monolithic* package over the same composite cell
  directory `CmaCells` as `cmaSim`. The state shape therefore matches
  `cmaSim`'s on the nose, so H3 reduces to a direct application of the
  heap-native identical-until-bad bridge
  (`VCVio/HeapSSP/IdenticalUntilBad.lean`) with a designated `.bad` cell.
  No inter-game state bijection is needed.

## Packages

* `nma hr` — no-message-attack game. Exports `nmaSpec`, imports `unifSpec`.
  State: `Heap (InnerCell M Commit Chal Stmt Wit)`, cells `.roCache /
  .keypair / .bad`. On `progSpec` queries, OR-updates `.bad` on a cache
  collision.
* `cmaToNma simT` — CMA-to-NMA reduction. Exports `cmaSpec`, imports
  `nmaSpec`. State: `Heap (OuterCell M)`, cell `.log`. Forwards non-sign
  queries unchanged; on sign queries samples the HVZK simulator and
  installs its challenge via `progSpec`.
* `cmaSim hr simT` — simulated CMA game, *defined* as
  `cmaToNma.link nma`. State: `Heap (CmaCells M Commit Chal Stmt Wit) =
  Heap (OuterCell M ⊕ InnerCell …)`.
* `cmaReal σ hr` — real CMA game. State: `Heap (CmaCells …)`, same shape
  as `cmaSim`. On sign queries runs the actual Σ-protocol (commit /
  RO-query / respond) and updates `.log`. The `.bad` cell is written but
  only ever to `false`: real signing never programs the RO.

## Composition identity (H4)

`cmaSim = cmaToNma.link nma` is *the* definition of `cmaSim`. The
program-equivalence hop

    `(cmaSim …).run A = (nma …).run ((cmaToNma …).shiftLeft A)`

then falls out of `HeapSSP.Package.run_link_eq_run_shiftLeft` applied to
`cmaToNma` and `nma`. No per-state-bijection scaffolding is needed.

## Identical-until-bad structure (H3)

`cmaReal` and `cmaSim` share the same state type
`Heap (CmaCells M Commit Chal Stmt Wit)`. The identical-until-bad bridge
(`Sigma/HeapSSP/Hops.lean`) supplies a bijection `φ : Heap CmaCells ≃
((List M) × (roSpec …).QueryCache × Option (Stmt × Wit)) × Bool` that
extracts the `.bad` cell, and discharges the pointwise-equal /
bad-monotone / per-query TV-distance obligations directly on the heap
handlers.
-/

universe u

open OracleSpec OracleComp ProbComp VCVio.HeapSSP

namespace FiatShamir.HeapSSP

variable (M : Type) [DecidableEq M]
variable (Commit : Type) [DecidableEq Commit]
variable (Chal : Type) [SampleableType Chal]
variable {Stmt Wit : Type} {rel : Stmt → Wit → Bool}
variable {Resp PrvState : Type}

/-! ### `nma`: no-message-attack game -/

/-- The no-message-attack game, as a `HeapSSP.Package` over the inner cell
directory `InnerCell M Commit Chal Stmt Wit`. No signing oracle; only
random-oracle, programming channel (used internally by `cmaToNma`), and
public-key oracle.

State cells:
* `.roCache` — the RO cache `(roSpec M Commit Chal).QueryCache`
* `.keypair` — lazily-sampled `Option (Stmt × Wit)`
* `.bad`     — `Bool`, OR-updated on programming collision

The external NMA adversary used by the H5 forking-lemma bridge interacts
with this game through only the `unifSpec + roSpec + pkSpec` sub-portion
of `nmaSpec`; `progSpec` is private to the CMA-to-NMA reduction. -/
noncomputable def nma
    (hr : GenerableRelation Stmt Wit rel) :
    Package unifSpec (nmaSpec M Commit Chal Stmt)
      (InnerCell M Commit Chal Stmt Wit) where
  init := pure Heap.empty
  impl
    | Sum.inl (Sum.inl (Sum.inl n)) => StateT.mk fun h => do
        let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
        pure (r, h)
    | Sum.inl (Sum.inl (Sum.inr mc)) => StateT.mk fun h =>
        let cache := h .roCache
        match cache mc with
        | some r => pure (r, h)
        | none => do
            let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            pure (r, h.update .roCache (cache.cacheQuery mc r))
    | Sum.inl (Sum.inr mch) => StateT.mk fun h =>
        let mc : M × Commit := (mch.1, mch.2.1)
        let ch : Chal := mch.2.2
        let cache := h .roCache
        match cache mc with
        | some _ => pure ((), h.update .bad true)
        | none => pure ((), h.update .roCache (cache.cacheQuery mc ch))
    | Sum.inr () => StateT.mk fun h =>
        match h .keypair with
        | some (pk, _) => pure (pk, h)
        | none => do
            let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
            pure (pk, h.update .keypair (some (pk, sk)))

/-! ### `cmaToNma`: CMA-to-NMA reduction -/

/-- The CMA-to-NMA reduction package, parameterized by the HVZK simulator
`simT`. Exports `cmaSpec`, imports `nmaSpec`, state `Heap (OuterCell M)`
holding only the signed-message log.

Forwards uniform sampling, RO hash queries, and public-key queries
verbatim through the import channel. On a sign query, samples a full
simulator transcript `(c, ch, π) ← simT pk`, installs the FS challenge
via the `progSpec` channel (which fires `bad` in `nma` on collision),
and appends the message to the local log. -/
noncomputable def cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    Package (nmaSpec M Commit Chal Stmt) (cmaSpec M Commit Chal Resp Stmt)
      (OuterCell M) where
  init := pure Heap.empty
  impl
    | Sum.inl (Sum.inl (Sum.inl n)) => StateT.mk fun h => do
        let r ← (((nmaSpec M Commit Chal Stmt).query (Sum.inl (Sum.inl (Sum.inl n)))) :
          OracleComp (nmaSpec M Commit Chal Stmt) (Fin (n + 1)))
        pure (r, h)
    | Sum.inl (Sum.inl (Sum.inr mc)) => StateT.mk fun h => do
        let r ← (((nmaSpec M Commit Chal Stmt).query (Sum.inl (Sum.inl (Sum.inr mc)))) :
          OracleComp (nmaSpec M Commit Chal Stmt) Chal)
        pure (r, h)
    | Sum.inl (Sum.inr m) => StateT.mk fun h => do
        let pk ← (((nmaSpec M Commit Chal Stmt).query (Sum.inr ())) :
          OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
        let (c, ch, π) ← (liftM (simT pk) :
          OracleComp (nmaSpec M Commit Chal Stmt) (Commit × Chal × Resp))
        let _ ← (((nmaSpec M Commit Chal Stmt).query (Sum.inl (Sum.inr (m, c, ch)))) :
          OracleComp (nmaSpec M Commit Chal Stmt) Unit)
        pure ((c, π), h.update .log (h .log ++ [m]))
    | Sum.inr () => StateT.mk fun h => do
        let pk ← (((nmaSpec M Commit Chal Stmt).query (Sum.inr ())) :
          OracleComp (nmaSpec M Commit Chal Stmt) Stmt)
        pure (pk, h)

/-! ### `cmaSim`: simulated CMA game

Defined structurally as `cmaToNma.link nma`. By construction its state
type is `Heap (OuterCell M ⊕ InnerCell …) = Heap (CmaCells …)` verbatim
(via `Heap.split`), matching `cmaReal`'s state type so that H3 applies
directly. H4 (program-equivalence with the shifted adversary) is then a
direct instance of `Package.run_link_eq_run_shiftLeft`. -/

/-- The simulated CMA game. **Definitionally** equal to
`cmaToNma.link nma`; this is the move that collapses H4 to an
invocation of the generic `run_link_eq_run_shiftLeft` lemma. -/
noncomputable abbrev cmaSim
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    Package unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (CmaCells M Commit Chal Stmt Wit) :=
  (cmaToNma M Commit Chal simT).link (nma M Commit Chal hr)

/-! ### `cmaReal`: real CMA game

Monolithic package over the composite cell directory `CmaCells`. State
shape matches `cmaSim`'s on the nose, so the identical-until-bad bridge
(`VCVio/HeapSSP/IdenticalUntilBad.lean`) applies with a bijection
`φ : Heap CmaCells ≃ σ × Bool` that projects the `.bad` cell. -/

/-- The real CMA game. On sign queries, runs the actual Σ-protocol:
(1) fetch or lazily sample the keypair in `.inr .keypair`; (2) run
`σ.commit`; (3) look up or lazily sample the RO challenge at `(m, c)` in
`.inr .roCache`; (4) run `σ.respond`; (5) append `m` to `.inl .log`.
The `.inr .bad` cell is never written: real signing does not program the
RO. -/
noncomputable def cmaReal
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) :
    Package unifSpec (cmaSpec M Commit Chal Resp Stmt)
      (CmaCells M Commit Chal Stmt Wit) where
  init := pure Heap.empty
  impl
    | Sum.inl (Sum.inl (Sum.inl n)) => StateT.mk fun h => do
        let r ← (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
        pure (r, h)
    | Sum.inl (Sum.inl (Sum.inr mc)) => StateT.mk fun h =>
        let cache := h (Sum.inr .roCache)
        match cache mc with
        | some r => pure (r, h)
        | none => do
            let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            pure (r, h.update (Sum.inr .roCache) (cache.cacheQuery mc r))
    | Sum.inl (Sum.inr m) => StateT.mk fun h => do
        let (pk, sk, h₁) ← match h (Sum.inr .keypair) with
          | some (pk, sk) =>
              (pure (pk, sk, h) :
                OracleComp unifSpec
                  (Stmt × Wit × Heap (CmaCells M Commit Chal Stmt Wit)))
          | none => do
              let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
              pure (pk, sk, h.update (Sum.inr .keypair) (some (pk, sk)))
        let (c, prvSt) ← (liftM (σ.commit pk sk) :
          OracleComp unifSpec (Commit × PrvState))
        let cache₁ := h₁ (Sum.inr .roCache)
        let (ch, h₂) ← match cache₁ (m, c) with
          | some r =>
              (pure (r, h₁) :
                OracleComp unifSpec
                  (Chal × Heap (CmaCells M Commit Chal Stmt Wit)))
          | none => do
              let r ← (($ᵗ Chal) : OracleComp unifSpec Chal)
              pure (r,
                h₁.update (Sum.inr .roCache) (cache₁.cacheQuery (m, c) r))
        let π ← (liftM (σ.respond pk sk prvSt ch) :
          OracleComp unifSpec Resp)
        pure ((c, π), h₂.update (Sum.inl .log) (h₂ (Sum.inl .log) ++ [m]))
    | Sum.inr () => StateT.mk fun h =>
        match h (Sum.inr .keypair) with
        | some (pk, _) => pure (pk, h)
        | none => do
            let (pk, sk) ← (hr.gen : OracleComp unifSpec _)
            pure (pk, h.update (Sum.inr .keypair) (some (pk, sk)))

/-! ### `cmaSim` init reduces to `pure Heap.empty`

Both `cmaToNma` and `nma` have `init = pure Heap.empty`, and
`simulateQ` on `pure` leaves the heap untouched, so the composite init
`(cmaToNma.link nma).init` reduces to `pure Heap.empty`. This is the
form needed to discharge the bridge's `h_init` hypotheses in
`Sigma/HeapSSP/Hops.lean`. -/

lemma cmaSim_init_eq
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (cmaSim M Commit Chal hr simT).init = pure Heap.empty := by
  change ((cmaToNma M Commit Chal simT).link (nma M Commit Chal hr)).init = _
  simp only [cmaToNma, nma, Package.link_init, pure_bind, simulateQ_pure, StateT.run_pure]
  rfl

end FiatShamir.HeapSSP
