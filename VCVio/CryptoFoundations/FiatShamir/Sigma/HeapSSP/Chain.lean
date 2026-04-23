/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Bridge
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Hops
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.Sigma.Security
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.HeapSSP.Composition

/-!
# HeapSSP Chain: H5 and the top-level EUF-CMA-to-Fork bound

Endpoint of the HeapSSP-style Fiat-Shamir EUF-CMA proof: chains
H1+H2+H3+H4+H5 to produce the EUF-CMA-to-`Fork.advantage` bound.

State access is heap-based. `cmaRealRun` packages the signed-message
log via `p.2 (Sum.inl .log)`; the `hProj` step in the final chain
reduction reads off the `.inl .log` cell verbatim. H4 is a direct
instance of `Package.run_link_eq_run_shiftLeft`, so no per-state
equivalence scaffolding is needed.

## Contents

* `nmaAdvFromCma` — reduction construction: from a CMA adversary and an
  HVZK simulator, build a managed-RO NMA adversary suitable as input
  to the replay-forking lemma (`Fork.replayForkingBound`).
* `nma_runProb_shiftLeft_signedAdv_le_fork` — **H5 hop**: bounds the
  NMA-side probability of accepting a forgery by
  `Fork.advantage σ hr M nmaAdv qH + δ_verify`; kept as `sorry` pending
  the forking-lemma reduction proof.
* `cma_advantage_le_fork_bound` — **top-level chain**. Tight
  Pointcheval-Stern-with-HVZK bound assembled from H1+H2+H3+H4+H5.
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.HeapSSP

namespace FiatShamir.HeapSSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [Fintype Chal] [Inhabited Chal]

/-! ### H5 hop: NMA advantage ≤ `Fork.advantage + δ_verify` -/

/-- The CMA-to-NMA reduction at the managed-RO interface.

Builds a `SignatureAlg.managedRoNmaAdv` from a CMA adversary `adv` and
an HVZK simulator `simT`. Internally this runs `adv` against the
simulator-replacement signing oracle and the programming-tracking RO,
collecting the programmed cache entries in `advCache` and returning
the adversary's forgery.

Concretely, it is the composition `cmaToNma.shiftLeft (signedAdv …)`
re-routed from `nmaSpec = unifSpec + roSpec + progSpec + pkSpec` to
the managed-RO `FiatShamir` spec `unifSpec + (M × Commit →ₒ Chal)`:

* `unifSpec`, `roSpec` queries pass through unchanged;
* `progSpec (m, c, ch)` queries are absorbed into `advCache`
  (deterministic write, no side-effect on the live RO);
* `pkSpec ()` queries return the fixed `pk` input parameter.

The `advCache` output is the union of all entries installed by the
simulator across signing queries, packaged as the managed-RO cache
consumed by `managedRoNmaExp`.

Alias for `FiatShamir.simulatedNmaAdv` under the HeapSSP-namespace
spelling used by the chain theorem below. -/
noncomputable def nmaAdvFromCma
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
  FiatShamir.simulatedNmaAdv σ hr M simT adv

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for the reduction `nmaAdvFromCma`.

The reduction forwards `qH` live hash queries from `adv`'s `roSpec`
channel plus `qS` live hash queries from sign-query simulator
transcripts (one per signing query, absorbed into `advCache` rather
than issued live). Net live `roSpec` query budget therefore stays at
`qH`.

This is the `nmaHashQueryBound` hypothesis consumed by
`Fork.replayForkingBound`. -/
theorem nmaAdvFromCma_nmaHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := Prod.fst <$> (nmaAdvFromCma σ hr M adv simT).main pk) qH := by
  intro pk
  have hbase :=
    FiatShamir.simulatedNmaAdv_hashQueryBound σ hr M simT adv qS qH hQ pk
  simpa [nmaHashQueryBound, nmaAdvFromCma] using hbase

/-- **H5 hop**: NMA-side forgery-acceptance probability is bounded by
`Fork.advantage + δ_verify`.

Running `nma` against `cmaToNma.shiftLeft (signedAdv σ hr M adv)`
returns a `ProbComp` whose `verify = true` event has probability
decomposed as:

* `Fork.advantage σ hr M (nmaAdvFromCma … adv simT) qH` — forgeries
  verifying through a challenge value present in the live query log
  (≤ qH entries), rewindable by the replay-forking lemma.
* `δ_verify` — residual event where the forgery's hash point was
  never queried live, so final verification lands on a fresh uniform
  challenge; bounded by `SigmaProtocol.verifyChallengePredictability σ
  δ_verify`.

Proof outline:

1. Split the event `verify = true` by whether the forgery's hash point
   `(msg, c)` was ever queried live during the simulation.
2. For the "queried live" branch, the verifying challenge matches the
   live cache entry at some index `s ≤ qH`; this is exactly the success
   event of `Fork.exp` (from `Sigma/Fork.lean`), so the branch's
   probability equals `Fork.advantage σ hr M (nmaAdvFromCma …) qH`.
3. For the "not queried live" branch, verification samples a fresh
   uniform `Chal`; acceptance probability at any fixed
   `(x, c, resp)` is at most `δ_verify` by
   `verifyChallengePredictability`.
4. The decomposition is tight: the two branches are disjoint, so the
   two bounds add without a union-bound factor. -/
theorem nma_runProb_shiftLeft_signedAdv_le_fork
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (δ_verify : ENNReal)
    (_hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify) :
    Pr[fun p : (M × (Commit × Resp)) × Bool => p.2 = true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
            (signedAdv σ hr M adv))]
      ≤ Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify := by
  sorry

/-! ### Top-level chain: H1 + H2 + H3 + H4 + H5 -/

/-- **Top-level HeapSSP chain** — tight EUF-CMA-to-Fork bound.

HeapSSP-native counterpart of `FiatShamir.euf_cma_to_nma`
(see `Sigma/Security.lean`). The chain is:

  `H1` (drop-fresh)                     +0
    ≤ `H2` (`unforgeableExpNoFresh = cmaReal.runProb signedAdv`)   +0
    ≤ `H3` (identical-until-bad, HVZK + cache-collision)
          +`qS · ζ_zk + qS · (qS + qH) · β`
    = `H4` (`cmaSim = cmaToNma.link nma`)           +0
    ≤ `H5` (fork + fresh-challenge)
          +`Fork.advantage σ hr M (nmaAdvFromCma …) qH + δ_verify`

Summing the per-hop slacks delivers the tight bound:

  `adv.advantage (runtime M)  ≤
    Fork.advantage σ hr M (nmaAdvFromCma …) qH
      + ENNReal.ofReal (qS · ζ_zk)
      + qS · (qS + qH) · β
      + δ_verify`.

Downstream, composing with `FiatShamir.euf_nma_bound` (the forking
lemma with special soundness) yields `FiatShamir.euf_cma_bound`. -/
theorem cma_advantage_le_fork_bound
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
    (δ_verify : ENNReal)
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    -- `hQB`: translated query bound on the Bool-valued adversary
    -- `Prod.snd <$> signedAdv`. This is the H3 sign-query hypothesis,
    -- obtainable from `hQ` by tracking `signedAdv`'s pre/post-keygen
    -- layout (1 pkSpec + lifted `adv.main pk` + liftM verify). Left as
    -- an assumption at this layer so that the chain's arithmetic is
    -- independent of the bound-translation bookkeeping.
    (hQB : OracleComp.IsQueryBound
      ((Prod.snd : (M × (Commit × Resp)) × Bool → Bool) <$> signedAdv σ hr M adv) qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b))
    -- `hQBH`: translated hash-query bound on the same Bool-valued
    -- adversary. Obtained from `hQ` by the same layout-tracking
    -- argument; left as an assumption at this layer.
    (hQBH : OracleComp.IsQueryBound
      ((Prod.snd : (M × (Commit × Resp)) × Bool → Bool) <$> signedAdv σ hr M adv) qH
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := Prod.fst <$> nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β +
          δ_verify := by
  refine ⟨nmaAdvFromCma σ hr M adv simT,
    nmaAdvFromCma_nmaHashQueryBound σ hr M adv simT qS qH hQ, ?_⟩
  set A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    Prod.snd <$> signedAdv σ hr M adv with hA_def
  have hCommit : σ.simCommitPredictability simT β := hPredSim
  have hζ_zk_lt : ENNReal.ofReal ζ_zk < ∞ := ENNReal.ofReal_lt_top
  have hHVZK' : σ.HVZK simT (ENNReal.ofReal ζ_zk).toReal := by
    rwa [ENNReal.toReal_ofReal hζ_zk]
  have hH3_abs :
      ENNReal.ofReal
          (((cmaReal M Commit Chal σ hr).runProb A).boolDistAdvantage
            ((cmaSim M Commit Chal hr simT).runProb A))
        ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β :=
    cmaReal_cmaSim_advantage_le_H3_bound M Commit Chal σ hr simT
      (ENNReal.ofReal ζ_zk) β hζ_zk_lt hHVZK' hCommit A qS qH hQB hQBH
  have hH3_prob : Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] ≤
      Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β) :=
    le_trans
      (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        ((cmaReal M Commit Chal σ hr).runProb A)
        ((cmaSim M Commit Chal hr simT).runProb A))
      (add_le_add le_rfl hH3_abs)
  have hH4 := cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma M Commit Chal hr simT
    (A := A)
  have hH4_pr : Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] =
      Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] :=
    probOutput_congr rfl (congrArg evalDist hH4)
  have hA_fst_snd : A = (Prod.snd ∘ id) <$> signedAdv σ hr M adv := by
    rw [hA_def]; rfl
  have hH5' :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] ≤
        Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify := by
    have hShift := (cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft_map
      (Prod.snd : (M × (Commit × Resp)) × Bool → Bool) (signedAdv σ hr M adv)
    have hRun := (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb_map
      (Prod.snd : (M × (Commit × Resp)) × Bool → Bool)
      ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft (signedAdv σ hr M adv))
    have hA_eq : A = Prod.snd <$> signedAdv σ hr M adv := hA_def
    rw [hA_eq, hShift, hRun]
    rw [probOutput_map_eq_tsum_ite]
    -- Now goal: `∑' x, (if true = x.2 then Pr[= x | ...] else 0) ≤ Fork.adv + δ_v`.
    -- Convert back to probEvent.
    have : Pr[= true |
        Prod.snd (α := M × (Commit × Resp)) (β := Bool) <$>
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft (signedAdv σ hr M adv))] =
      Pr[fun p : (M × (Commit × Resp)) × Bool => p.2 = true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft (signedAdv σ hr M adv))] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]; rfl
    rw [← probOutput_map_eq_tsum_ite]
    rw [this]
    exact nma_runProb_shiftLeft_signedAdv_le_fork σ hr M adv simT qS qH hQ
      δ_verify hVerifyGuess
  have hH1H2 : adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := by
    have h12 := cma_advantage_le_runProb_cmaRealNoFresh (M := M) σ hr adv
    have h_eq : Pr[= true |
          (fun p : (M × (Commit × Resp)) × Bool × List M => p.2.1) <$>
            cmaRealRun σ hr M adv] =
        Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := by
      have hProj :
          (fun p : (M × (Commit × Resp)) × Bool × List M => p.2.1) <$>
              cmaRealRun σ hr M adv =
            (cmaReal M Commit Chal σ hr).runProb A := by
        -- LHS reduces to `(fun q => q.1.2) <$> runState signedAdv` after
        -- unfolding `cmaRealRun` and eliminating the pure bind.
        -- RHS: `runProb (Prod.snd <$> signedAdv) = Prod.snd <$> runProb signedAdv`
        --   (runProb_map)
        -- `= Prod.snd <$> (Prod.fst <$> runState signedAdv)`
        -- `= (fun q => q.1.2) <$> runState`.
        rw [hA_def, Package.runProb_map]
        unfold cmaRealRun
        rw [map_bind]
        simp only [map_pure, bind_pure_comp]
        change
          ((fun q => q.1.2) <$>
              (cmaReal M Commit Chal σ hr).runState (signedAdv σ hr M adv)) =
            Prod.snd <$> (cmaReal M Commit Chal σ hr).runProb (signedAdv σ hr M adv)
        unfold Package.runProb Package.run Package.runState
        rw [map_bind, map_bind]
        refine bind_congr fun _ => ?_
        rw [StateT.run'_eq, Functor.map_map]
      rw [hProj]
    exact h_eq ▸ h12
  calc adv.advantage (FiatShamir.runtime M)
      ≤ Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := hH1H2
    _ ≤ Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β) := hH3_prob
    _ = Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β) := by
        rw [hH4_pr]
    _ ≤ (Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify) +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β) :=
        add_le_add hH5' le_rfl
    _ = Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β +
          δ_verify := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (qS : ℝ)),
            show ENNReal.ofReal (qS : ℝ) = (qS : ENNReal) from
              ENNReal.ofReal_natCast _]
        ring

end FiatShamir.HeapSSP
