/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Games
import VCVio.HeapSSP.Advantage

/-!
# Bridge between `unforgeableExp` and `cmaReal.runProb` (HeapSSP)

Ties the existing `SignatureAlg.unforgeableAdv`-based EUF-CMA experiment
for the Fiat-Shamir scheme to the HeapSSP `cmaReal` game
(`Sigma/HeapSSP/Games.lean`). Contributes hops H1 and H2 of the SSP plan:

* **H1 (drop-fresh)**: wraps
  `SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh` for
  the FS scheme. Independent of the internal state representation.
* **H2 (`unforgeableExp` ↔ `cmaReal.runProb`)**: expresses the
  unforgeability experiment as `cmaReal.runState`-with-post-check, with
  the signed-message log read off `cmaReal`'s `.inl .log` heap cell.

The `cmaReal.impl` is monolithic (single
`QueryImpl cmaSpec (StateT (Heap CmaCells) …)`), so the
`pkSpec`-factoring helper lemmas are phrased directly on
`(cmaReal.impl (Sum.inr ()))` rather than on a dedicated sub-handler.
-/

universe u v

open OracleSpec OracleComp ProbComp VCVio.HeapSSP

namespace FiatShamir.HeapSSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
variable [SampleableType Chal]

/-! ### HeapSSP-side adversary -/

/-- Lift a CMA-style `unforgeableAdv` for the Fiat-Shamir scheme into an
adversary against the HeapSSP `cmaReal` game.

The wrapper:
1. Issues a `pkSpec` query to obtain the public key from `cmaReal`'s
   lazily-sampled keypair (stored in the `.inr .keypair` cell).
2. Lifts the source adversary's `main pk` into `OracleComp cmaSpec ...`
   via the canonical `(unifSpec + roSpec) + signSpec ⊂ₒ cmaSpec`
   `SubSpec` embedding.
3. Runs FS verification, which issues one further `roSpec` query
   through the same RO cache (in `.inr .roCache`).
4. Returns the forgery paired with the verification bit. The freshness
   post-check is read off `cmaReal`'s log cell externally
   (see `cmaRealRun`). -/
@[reducible] noncomputable def signedAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let pk ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

/-- Instrument a `cmaSpec` computation with a local list of signing-query
messages while forwarding every query to the surrounding `cmaSpec`.

This is deliberately adversary-side logging: it records the signing queries
visible in the syntax of the adversary computation, not the package's private
heap log. Keeping this log in the output lets the H3 Boolean-output bridge
reason about freshness without a separate final-state event theorem. -/
@[reducible] noncomputable def cmaSignLogImpl :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M) (OracleComp (cmaSpec M Commit Chal Resp Stmt)))
  | Sum.inl (Sum.inl (Sum.inl n)) => do
      let r ← (((cmaSpec M Commit Chal Resp Stmt).query
        (Sum.inl (Sum.inl (Sum.inl n)))) :
          OracleComp (cmaSpec M Commit Chal Resp Stmt) (Fin (n + 1)))
      pure r
  | Sum.inl (Sum.inl (Sum.inr mc)) => do
      let r ← (((cmaSpec M Commit Chal Resp Stmt).query
        (Sum.inl (Sum.inl (Sum.inr mc)))) :
          OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)
      pure r
  | Sum.inl (Sum.inr m) => do
      let signed ← get
      let sig ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl (Sum.inr m))) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) (Commit × Resp))
      set (signed ++ [m])
      pure sig
  | Sum.inr () => do
      let pk ← (((cmaSpec M Commit Chal Resp Stmt).query (Sum.inr ())) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Stmt)
      pure pk

/-- Freshness-preserving Boolean adversary for the HeapSSP CMA chain.

It runs `signedAdv`, locally logs all signing-query messages, and returns
`true` exactly when the final forgery verifies and its message was not among
the locally logged signing queries. This is the Boolean game that should flow
through H3/H4/H5; using the no-fresh `verified` bit here would make the H5
forking hop false for replay adversaries. -/
@[reducible] noncomputable def signedFreshAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool := do
  let p : ((M × (Commit × Resp)) × Bool) × List M ←
    (simulateQ (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt)) (signedAdv σ hr M adv)).run []
  let out := p.1
  let signed := p.2
  pure (!decide (out.1.1 ∈ signed) && out.2)

/-! ### Joint output of `cmaReal` -/

/-- Run `cmaReal` against `signedAdv` and pack the resulting forgery,
verification bit, and signed-message log into a single `ProbComp`.

The signed-message log lives in `cmaReal`'s `.inl .log` heap cell and
is the freshness witness that `unforgeableExp` carries in a `WriterT`
instead. -/
@[reducible] noncomputable def cmaRealRun
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    ProbComp ((M × (Commit × Resp)) × Bool × List M) := do
  let p ← (cmaReal M Commit Chal σ hr).runState (signedAdv σ hr M adv)
  pure (p.1.1, p.1.2, p.2 (Sum.inl .log))

/-! ### Bridge equalities

Factor out the lazy keygen step: the first query issued by `signedAdv`
is the `pkSpec` one, so on the empty initial heap `cmaReal.impl` runs
`hr.gen` and installs the keypair in the `.inr .keypair` cell. Every
subsequent query sees the same keypair. -/

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The `pkSpec` branch of `cmaReal.impl` on a heap with `.keypair = none`
calls `hr.gen` and updates the `.keypair` cell. -/
private lemma cmaReal_impl_pkSpec_none_run
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hkp : h (Sum.inr .keypair) = none) :
    (((cmaReal M Commit Chal σ hr).impl (Sum.inr () :
        (cmaSpec M Commit Chal Resp Stmt).Domain))).run h =
      hr.gen >>= fun ps : Stmt × Wit =>
        pure (ps.1, h.update (Sum.inr .keypair) (some (ps.1, ps.2))) := by
  simp only [cmaReal, StateT.run_mk, hkp]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The `pkSpec` branch of `cmaReal.impl` on a heap with `.keypair = some (pk, sk)`
returns the public key without touching the heap. -/
private lemma cmaReal_impl_pkSpec_some_run
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (pk : Stmt) (sk : Wit)
    (hkp : h (Sum.inr .keypair) = some (pk, sk)) :
    (((cmaReal M Commit Chal σ hr).impl (Sum.inr () :
        (cmaSpec M Commit Chal Resp Stmt).Domain))).run h =
      pure (pk, h) := by
  simp only [cmaReal, StateT.run_mk, hkp]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Threading a continuation `f` through the `pkSpec` branch of
`cmaReal.impl` on an empty-keypair heap extracts the `hr.gen` step. -/
private lemma cmaReal_impl_pkSpec_bind_run_none {α : Type}
    (f : Stmt → StateT (Heap (CmaCells M Commit Chal Stmt Wit))
      (OracleComp unifSpec) α)
    (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (hkp : h (Sum.inr .keypair) = none) :
    ((cmaReal M Commit Chal σ hr).impl
        (Sum.inr () : (cmaSpec M Commit Chal Resp Stmt).Domain) >>= f) h =
      hr.gen >>= fun ps : Stmt × Wit =>
        (f ps.1).run (h.update (Sum.inr .keypair) (some (ps.1, ps.2))) := by
  change ((cmaReal M Commit Chal σ hr).impl
      (Sum.inr () : (cmaSpec M Commit Chal Resp Stmt).Domain)).run h >>=
    (fun vs => (f vs.1).run vs.2) = _
  rw [cmaReal_impl_pkSpec_none_run (σ := σ) (hr := hr) (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) h hkp]
  simp

/-- The "post-keygen" portion of `signedAdv`: the adversary's main routine
followed by FS verification, with `pk` already fixed. All queries are
through `cmaSpec`; the `pkSpec` summand is never touched again. -/
@[reducible] noncomputable def postKeygenAdv
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) ((M × (Commit × Resp)) × Bool) := do
  let (msg, sig) ← (liftM (adv.main pk) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))
  let verified ← (liftM
    ((FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
      pk msg sig) :
    OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
  pure ((msg, sig), verified)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The first `pkSpec` query in `signedAdv` forces `cmaReal` to run its lazy
keygen, installing a stable `some (pk, sk)` in the `.inr .keypair` cell.
The rest of `signedAdv` (adversary's main + FS verification) never
touches `pkSpec`, so we can factor the keygen out as a top-level
`hr.gen` bind. -/
private lemma cmaRealRun_eq_keygen_bind
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    cmaRealRun σ hr M adv =
      (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        (simulateQ (cmaReal M Commit Chal σ hr).impl
            (postKeygenAdv σ hr M adv ps.1)).run
          (Heap.empty.update (Sum.inr .keypair) (some (ps.1, ps.2))) >>=
          fun p => pure (p.1.1, p.1.2, p.2 (Sum.inl .log)) := by
  unfold cmaRealRun signedAdv Package.runState postKeygenAdv
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run]
  -- `cmaReal.init = pure Heap.empty` definitionally; reduce the outer init.
  change ((pure (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)) :
      OracleComp unifSpec _) >>= fun h₀ => _) >>= _ = _
  simp only [pure_bind]
  rw [cmaReal_impl_pkSpec_bind_run_none (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) _ _ rfl]
  simp only [bind_assoc]
  rfl

/-- Hop **H2** (freshness-preserving): running the syntactically logged
Boolean adversary through `cmaReal` matches the original Fiat-Shamir
EUF-CMA experiment.

The top-level proof reduces to matching:

1. the `pkSpec` handler (lazy vs eager keygen), captured by
   `cmaRealRun_eq_keygen_bind` above;
2. the RO cache handler (`.inr .roCache` in the heap vs
   `Context.randomOracle` in `runtime`);
3. the signing handler (runs FS signing through the same RO cache vs
   `signingOracle pk sk` in a `WriterT` log);
4. the verify call (one further `Hash (msg, c)` through the same cache);
5. the signing-query log produced by `cmaSignLogImpl` against the
   `WriterT` log in `SignatureAlg.unforgeableExp`.

Kept as `sorry` pending the full distributional proof; the body reuses
the FS-specific `signedAppend` /
`map_run_withLogging_inputs_eq_run_signedAppend` lemma chain from
`Sigma/Security.lean`. -/
theorem cmaRealFreshAdvantage_eq_unforgeableExp
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    Pr[= true | (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv)] =
      adv.advantage (FiatShamir.runtime M) := by
  sorry

/-! ### H1 + H2 composition -/

/-- H2 in inequality form: the CMA advantage is bounded by the probability
that `cmaReal` accepts the freshness-preserving Boolean adversary. Entry
point for the rest of the HeapSSP hop chain
(`cmaReal → cmaSim → nma → Fork`). -/
theorem cma_advantage_le_runProb_cmaRealFresh
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb (signedFreshAdv σ hr M adv)] := by
  rw [cmaRealFreshAdvantage_eq_unforgeableExp]

end FiatShamir.HeapSSP
