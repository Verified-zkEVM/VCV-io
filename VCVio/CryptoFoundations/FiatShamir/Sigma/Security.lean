/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.CryptoFoundations.Fork
import VCVio.CryptoFoundations.ReplayFork

/-!
# EUF-CMA security of the Fiat-Shamir Σ-protocol transform

End-to-end security reduction, packaged as three theorems:

- `euf_cma_to_nma`: CMA-to-NMA via HVZK simulation, absorbing the signing-query
  loss into a statistical term `qS · ζ_zk + ζ_col`;
- `euf_nma_bound`: NMA-to-extraction via `Fork.replayForkingBound` and special
  soundness, producing a reduction to `hardRelationExp`;
- `euf_cma_bound`: the combined bound, instantiating `euf_cma_to_nma` into
  `euf_nma_bound`.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B) + qS · ζ_zk + ζ_col`

The NMA adversary `B` is constructed by:
- Forwarding `A`'s hash queries to the external oracle (visible to `Fork.fork`)
- Simulating `A`'s signing queries using the HVZK simulator, programming the
  simulated challenge into the cache
- Returning `A`'s forgery together with the accumulated `QueryCache`

Each of the `qS` signing simulations introduces at most `ζ_zk` total-variation distance.
The `ζ_col` term accounts for collisions where `A` queries a hash that `B` later programs.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`.

The Lean bound matches Firsov-Janku's `pr_koa_cma` at
[fsec/proof/Schnorr.ec:943](../../../fsec/proof/Schnorr.ec): the CMA-to-KOA reduction uses
`eq_except (signed qs) LRO.m{1} LRO.m{2}` as the RO-cache invariant, swaps real signing with
`simulator_equiv` (per-query HVZK cost), handles RO reprogramming via `lro_redo_inv` +
`ro_get_eq_except`, and absorbs the late-programming collision event through the `bad` flag,
bounded by `pr_bad_game` at [fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) as
`QS · (QS+QR) / |Ω|`, matching our `ζ_col`. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk ζ_col : ℝ) (_hζ_zk : 0 ≤ ζ_zk) (_hζ_col : 0 ≤ ζ_col)
    (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal (qS * ζ_zk + ζ_col) := by
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none =>
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  refine ⟨⟨fun pk => (simulateQ (baseSim + sigSim pk) (adv.main pk)).run ∅⟩, ?_, ?_⟩
  · -- Query bound: show the NMA adversary makes at most `qH` hash queries.
    -- `fwd` forwards each hash query as-is (1 hash query per CMA hash query).
    -- `sigSim` handles signing queries via `simTranscript` + cache programming,
    -- generating zero hash queries (only uniform queries from `simTranscript`).
    -- Requires a general `IsQueryBound` transfer lemma for `simulateQ` + `StateT.run`.
    intro pk
    let stepBudget :
        (spec + (M →ₒ (Commit × Resp))).Domain → ℕ × ℕ → ℕ := fun t _ =>
      match t with
      | .inl (.inl _) => 0
      | .inl (.inr _) => 1
      | .inr _ => 0
    have hbind :
        ∀ {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {Q₁ Q₂ : ℕ},
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁ →
          (∀ x, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ob x) Q₂) →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := oa >>= ob) (Q₁ + Q₂) := by
      intro α β oa ob Q₁ Q₂ h1 h2
      exact nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal) h1 h2
    have hfwd :
        ∀ (t : spec.Domain) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (fwd t).run s) (match t with
              | .inl _ => 0
              | .inr _ => 1) := by
      intro t s
      cases t with
      | inl n =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (query (spec := spec) (.inl n))) 0 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inl n) 0).2 trivial)
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
      | inr mc =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (query (spec := spec) (.inr mc))) 1 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inr mc) 1).2 (Nat.succ_pos 0))
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
    have hro :
        ∀ (mc : M × Commit) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (roSim mc).run s) 1 := by
      intro mc s
      cases hs : s (.inr mc) with
      | some v =>
          simp [roSim, hs, nmaHashQueryBound]
      | none =>
          simpa [roSim, hs] using
            ((OracleComp.isQueryBound_map_iff
                (oa := (fwd (.inr mc)).run s)
                (f := fun a : Chal × spec.QueryCache =>
                  (a.1, a.2.cacheQuery (.inr mc) a.1))
                (b := 1)
                (canQuery := fun t b => match t with
                  | .inl _ => True
                  | .inr _ => 0 < b)
                (cost := fun t b => match t with
                  | .inl _ => b
                  | .inr _ => b - 1)).2
              (hfwd (.inr mc) s))
    have hsig :
        ∀ (msg : M) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (sigSim pk msg).run s) 0 := by
      intro msg s
      have hsource : OracleComp.IsQueryBound
          (simTranscript pk) () (fun _ _ => True) (fun _ _ => ()) := by
        induction simTranscript pk using OracleComp.inductionOn with
        | pure x =>
            trivial
        | query_bind t mx ih =>
            simp [OracleComp.isQueryBound_query_bind_iff, ih]
      have htranscript :
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (simulateQ unifSim (simTranscript pk)).run s) 0 := by
        simpa [nmaHashQueryBound] using
          (OracleComp.IsQueryBound.simulateQ_run_of_step
            (h := hsource) (combine := Nat.add) (mapBudget := fun _ => 0)
            (stepBudget := fun _ _ => 0) (impl := unifSim)
            (hbind := by
              intro γ δ oa' ob b₁ b₂ h1 h2
              have h1' :
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := oa') b₁ := by
                simpa [nmaHashQueryBound] using h1
              have h2' : ∀ x,
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := ob x) b₂ := by
                intro x
                simpa [nmaHashQueryBound] using h2 x
              simpa [nmaHashQueryBound] using
                (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
            )
            (hstep := by
              intro t b s' ht
              simpa [unifSim] using hfwd (.inl t) s')
            (hcombine := by
              intro t b ht
              simp)
            (s := s))
      simpa [sigSim, nmaHashQueryBound] using
        ((OracleComp.isQueryBound_map_iff
            (oa := (simulateQ unifSim (simTranscript pk)).run s)
            (f := fun a : (Commit × Chal × Resp) × spec.QueryCache =>
              match a.2 (.inr (msg, a.1.1)) with
              | some _ => ((a.1.1, a.1.2.2), a.2)
              | none =>
                  ((a.1.1, a.1.2.2),
                    QueryCache.cacheQuery a.2 (.inr (msg, a.1.1)) a.1.2.1))
            (b := 0)
            (canQuery := fun t b => match t with
              | .inl _ => True
              | .inr _ => 0 < b)
            (cost := fun t b => match t with
              | .inl _ => b
              | .inr _ => b - 1)).2 htranscript)
    have hstep :
        ∀ t b s,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ((baseSim + sigSim pk) t).run s) (stepBudget t b) := by
      intro t b s ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simpa [baseSim, stepBudget] using hfwd (.inl n) s
          | inr mc =>
              simpa [baseSim, stepBudget] using hro mc s
      | inr msg =>
          simpa [stepBudget] using hsig msg s
    have hcombine :
        ∀ t b,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          Nat.add (stepBudget t b)
            (Prod.snd (match t, b with
              | .inl (.inl _), b' => b'
              | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
              | .inr _, (qS', qH') => (qS' - 1, qH'))) =
            Prod.snd b := by
      intro t b ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simp [stepBudget]
          | inr mc =>
              simp [stepBudget] at ht ⊢
              omega
      | inr msg =>
          simp [stepBudget]
    simpa [nmaHashQueryBound, signHashQueryBound] using
      (OracleComp.IsQueryBound.simulateQ_run_of_step
        (h := _hQ pk) (combine := Nat.add) (mapBudget := Prod.snd)
        (stepBudget := stepBudget) (impl := baseSim + sigSim pk)
        (hbind := by
          intro γ δ oa' ob b₁ b₂ h1 h2
          have h1' :
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := oa') b₁ := by
            simpa [nmaHashQueryBound] using h1
          have h2' : ∀ x,
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := ob x) b₂ := by
            intro x
            simpa [nmaHashQueryBound] using h2 x
          simpa [nmaHashQueryBound] using
            (hbind (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
        )
        (hstep := by
          intro t b s ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hfwd (.inl n) s
              | inr mc =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hro mc s
          | inr msg =>
              simpa [nmaHashQueryBound, stepBudget] using hsig msg s)
        (hcombine := by
          intro t b ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simp [stepBudget]
              | inr mc =>
                  simp [stepBudget] at ht ⊢
                  omega
          | inr msg =>
              simp [stepBudget])
        (s := ∅))
  · -- Advantage bound: `adv.advantage ≤ Adv^{fork-NMA}_{qH}(nmaAdv) + qS * ζ_zk + ζ_col`.
    --
    -- Proof plan:
    --
    -- (1) Drop freshness: `!log.wasQueried msg && verified ≤ verified`, so
    --     `adv.advantage ≤ Pr[verified | CMA signing, real RO verification]`.
    --     Use `probEvent_mono` or `probOutput_map_le` after unfolding `unforgeableExp`.
    --
    -- (2) Intermediate game: define `CMA-no-freshness` that uses the real signing
    --     oracle but returns only the verification bit. Both the CMA-no-freshness
    --     and NMA experiments can be expressed as
    --       `(runtime M).evalDist (keygen >>= fun (pk, sk) => game_X pk sk)`
    --     where `game_X` runs `adv.main pk` with oracle `impl_X` and then verifies.
    --
    -- (3) TV distance decomposition (triangle inequality):
    --     `tvDist(CMA-no-fresh, NMA) ≤ tvDist(CMA-no-fresh, hybrid) + tvDist(hybrid, NMA)`
    --     where `hybrid` uses the simulated signing oracle but verifies with the real RO
    --     (no cache overlay).
    --
    --     (3a) CMA-no-fresh → hybrid: signing oracle replacement.
    --          Each of `qS` signing queries changes from real signing (commit, hash, respond)
    --          to simulated signing (simTranscript, cache program). Per query, HVZK gives
    --          `ζ_zk` TV distance. Total: `qS * ζ_zk`.
    --          Needs `tvDist_bind_left_le` and per-query HVZK bounds.
    --
    --     (3b) hybrid → fork-NMA: relate successful fresh forgeries to the forkable
    --          experiment `Fork.exp`. The reduction now serves `A`'s live
    --          hash queries through the same managed cache it eventually returns, and
    --          `sigSim` preserves any pre-existing cache entry instead of overwriting it.
    --          The remaining discrepancy is exactly the late-programming collision event
    --          absorbed by the slack term `ζ_col`.
    --
    -- (4) Conclude:
    --       `adv.advantage ≤ Adv^{fork-NMA}_{qH}(nmaAdv)
    --          + ENNReal.ofReal (qS * ζ_zk + ζ_col)`.
    --     Use `abs_probOutput_toReal_sub_le_tvDist` to convert TV distance to ENNReal bound.
    sorry
section evalDistBridge

variable [Fintype Chal] [Inhabited Chal] [SampleableType Chal]

/-- The `ofLift + uniformSampleImpl` simulation on `unifSpec + (Unit →ₒ Chal)` preserves
`evalDist`. Both oracle components sample uniformly from their range (the `unifSpec`
side via `liftM (query n) : ProbComp (Fin (n+1))`, the challenge side via `$ᵗ Chal`),
so the simulated computation has the same distribution as the source. -/
private lemma evalDist_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) :
    evalDist (simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rcases t with n | u
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        id_map, evalDist_bind, ih]
      apply bind_congr
      simp
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inr, uniformSampleImpl,
        id_map, evalDist_bind, ih]
      have heq : (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
            SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
          (evalDist (liftM (query (Sum.inr u)) :
            OracleComp (unifSpec + (Unit →ₒ Chal)) _) :
            SPMF ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr u))) := by
        rw [evalDist_uniformSample, evalDist_query]; rfl
      exact heq ▸ rfl

/-- Corollary: `probEvent` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probEvent_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (p : α → Prop) :
    Pr[ p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator]
  refine tsum_congr fun x => ?_
  unfold Set.indicator
  split_ifs with hpx
  · exact congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x
  · rfl

/-- Corollary: `probOutput` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probOutput_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (x : α) :
    Pr[= x | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x

end evalDistBridge
section jensenIntegration

/-- **Keygen-indexed Cauchy-Schwarz / Jensen step for the forking lemma.**

Given a per-element bound `acc x · (acc x / q - hinv) ≤ B x`, integrating over a
probabilistic key-generator `gen : ProbComp X` yields the "lifted" bound:

  `μ · (μ / q - hinv) ≤ 𝔼[B]`

where `μ = 𝔼[acc] = ∑' x, Pr[= x | gen] · acc x`.

The proof goes through the convexity identity `μ² ≤ 𝔼[acc²]` (Cauchy-Schwarz on the
probability distribution `Pr[= · | gen]`), together with `ENNReal.mul_sub` to handle the
truncated subtraction. -/
private lemma jensen_keygen_forking_bound
    {X : Type} (gen : ProbComp X)
    (acc B : X → ENNReal) (q hinv : ENNReal)
    (hinv_ne_top : hinv ≠ ⊤)
    (hacc_le : ∀ x, acc x ≤ 1)
    (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∑' x, Pr[= x | gen] * acc x) *
        ((∑' x, Pr[= x | gen] * acc x) / q - hinv) ≤
      ∑' x, Pr[= x | gen] * B x := by
  classical
  set w : X → ENNReal := fun x => Pr[= x | gen] with hw_def
  set μ : ENNReal := ∑' x, w x * acc x with hμ_def
  have hw_tsum_le_one : ∑' x, w x ≤ 1 := tsum_probOutput_le_one
  have hμ_le_one : μ ≤ 1 := by
    calc μ = ∑' x, w x * acc x := rfl
      _ ≤ ∑' x, w x * 1 := by gcongr with x; exact hacc_le x
      _ = ∑' x, w x := by simp
      _ ≤ 1 := hw_tsum_le_one
  have hμ_ne_top : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le_one
  -- The integrand `w x * acc x * hinv`, with total sum `μ * hinv`.
  have hμ_hinv_ne_top : μ * hinv ≠ ⊤ := ENNReal.mul_ne_top hμ_ne_top hinv_ne_top
  -- Cauchy-Schwarz: `μ² ≤ ∑' w * acc²`.
  have hCS : μ ^ 2 ≤ ∑' x, w x * acc x ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w acc hw_tsum_le_one
  -- Split off the key reverse-Jensen inequality as an intermediate calc.
  -- Integrate the per-element bound.
  calc μ * (μ / q - hinv)
      = μ * (μ / q) - μ * hinv :=
        ENNReal.mul_sub (fun _ _ => hμ_ne_top)
    _ = μ ^ 2 / q - μ * hinv := by
        rw [sq, mul_div_assoc]
    _ ≤ (∑' x, w x * acc x ^ 2) / q - μ * hinv := by
        gcongr
    _ = (∑' x, w x * acc x ^ 2 / q) - ∑' x, w x * acc x * hinv := by
        congr 1
        · simp only [div_eq_mul_inv]
          rw [ENNReal.tsum_mul_right]
        · rw [hμ_def, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, (w x * acc x ^ 2 / q - w x * acc x * hinv) := by
        -- Reverse-Jensen: `∑' f - ∑' g ≤ ∑' (f - g)` in ENNReal when `∑' g ≠ ⊤`.
        set f : X → ENNReal := fun x => w x * acc x ^ 2 / q with hf_def
        set g : X → ENNReal := fun x => w x * acc x * hinv with hg_def
        have hg_sum_ne_top : ∑' x, g x ≠ ⊤ := by
          change ∑' x, w x * acc x * hinv ≠ ⊤
          rw [ENNReal.tsum_mul_right]; exact hμ_hinv_ne_top
        have hfg : ∑' x, f x ≤ ∑' x, (f x - g x) + ∑' x, g x := by
          calc ∑' x, f x ≤ ∑' x, ((f x - g x) + g x) := by
                exact ENNReal.tsum_le_tsum fun x => le_tsub_add
            _ = ∑' x, (f x - g x) + ∑' x, g x := ENNReal.tsum_add
        exact tsub_le_iff_right.2 hfg
    _ = ∑' x, w x * (acc x ^ 2 / q - acc x * hinv) := by
        refine tsum_congr fun x => ?_
        have hwx_ne_top : w x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
        rw [ENNReal.mul_sub (fun _ _ => hwx_ne_top), mul_div_assoc, mul_assoc]
    _ = ∑' x, w x * (acc x * (acc x / q - hinv)) := by
        refine tsum_congr fun x => ?_
        have hax_ne_top : acc x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (hacc_le x)
        congr 1
        rw [ENNReal.mul_sub (fun _ _ => hax_ne_top), sq, mul_div_assoc]
    _ ≤ ∑' x, w x * B x := by
        gcongr with x
        exact hper x

end jensenIntegration
/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any managed-RO NMA adversary `B` making at most `qH` random-oracle queries, there
exists a witness-extraction reduction such that:

  `Adv^{fork-NMA}_{qH}(B) · (Adv^{fork-NMA}_{qH}(B) / (qH + 1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

Runs `B.main pk` twice with shared randomness up to a randomly chosen fork point, then
re-samples the oracle answer. Programmed cache entries are part of `B`'s deterministic
computation given the seed, so they are identical across both fork runs. The reduction
extracts only from fork outputs whose two forged transcripts share a commitment and whose
cached challenges are distinct. The remaining proof obligation is to show that successful
forks satisfy exactly those compatibility checks, after which special soundness applies.

Here `Adv^{fork-NMA}_{qH}(B)` is `Fork.advantage`: it counts exactly the
managed-RO executions whose forgery already verifies from challenge values present in the
adversary's managed cache or in the live hash-query log recorded by
`Fork.runTrace`. This is the precise success event that the forking lemma can
rewind.

This matches Firsov-Janku's `schnorr_koa_secure` at
[fsec/proof/Schnorr.ec:448](../../../fsec/proof/Schnorr.ec), which applies `forking_lemma_ro`
with the single-run postcondition `verify` plus the extractor correctness lemma
`extractor_corr` at [fsec/proof/Schnorr.ec:87](../../../fsec/proof/Schnorr.ec). Our version
uses `Fork.replayForkingBound` for the RO-level packaging and `_hss` for special
soundness, with `σ.extract` playing the role of EC's `extractor`. -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (_hQ : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := nmaAdv.main pk) qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      (Fork.advantage σ hr M nmaAdv qH *
          (Fork.advantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) -
            challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  classical
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  -- Replay `nmaAdv` into a single-counted challenge oracle and record the rewindable trace.
  let wrappedMain : Stmt → OracleComp (unifSpec + (Unit →ₒ Chal))
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    Fork.runTrace σ hr M nmaAdv
  let cf : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      Option (Fin (qH + 1)) :=
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  -- ─── Replay-fork query budget ───
  -- Only the single counted challenge oracle is forked.
  let qb : ℕ ⊕ Unit → ℕ := fun | .inl _ => 0 | .inr () => qH
  -- ─── Replay-fork and extract ───
  -- Phase 1: replay-fork the wrapped adversary at the single challenge oracle,
  -- then extract a witness via special soundness.
  let forkExtract : Stmt → OracleComp (unifSpec + (Unit →ₒ Chal)) Wit := fun pk => do
    let result ← forkReplay (wrappedMain pk) qb (Sum.inr ()) cf
    match result with
    | none => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    | some (x₁, x₂) =>
      let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
      let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
      if hc : c₁ = c₂ then
        match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
        | some ω₁, some ω₂ =>
            if hω : ω₁ ≠ ω₂ then
              liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + chalSpec)
            else
              liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      else
        liftComp ($ᵗ Wit) (unifSpec + chalSpec)
  -- Phase 2: Convert to ProbComp by simulating the single challenge oracle
  -- with $ᵗ Chal (uniform challenge sampling).
  let reduction : Stmt → ProbComp Wit := fun pk =>
    simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := chalSpec))) (forkExtract pk)
  refine ⟨reduction, ?_⟩
  -- Phase 3: The probability bound, decomposed into four named steps (a)-(d).
  --
  -- Define the per-public-key acceptance probability used throughout.
  let acc : Stmt → ENNReal := fun pk => Pr[ fun x => (cf x).isSome | wrappedMain pk]
  -- ── Step (a): rewrite `Fork.advantage` as the expected per-pk
  -- acceptance `Pr[isSome ∘ cf | keygen >>= wrappedMain]`. This unfolds the
  -- `simulateQ` wrapping around the sum spec via `uniformSampleImpl.probEvent_simulateQ`
  -- and applies `probEvent_map` for the final `(·.isSome)` event.
  have hAdv_eq : Fork.advantage σ hr M nmaAdv qH =
      Pr[ fun (pt : Stmt × Fork.Trace
          (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            (cf pt.2).isSome | do
          let (pk, _) ← OracleComp.liftComp hr.gen (unifSpec + chalSpec)
          let trace ← wrappedMain pk
          pure (pk, trace)] := by
    change Pr[= true | Fork.exp σ hr M nmaAdv qH] = _
    unfold Fork.exp
    rw [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl]
    simp only [bind_pure_comp, probEvent_map, probEvent_bind_eq_tsum,
      Function.comp_def]
    rfl
  -- The strengthened per-run invariant `P_out pk x log`: when `cf x = some s`, the
  -- cached RO value at the forgery target agrees with the logged challenge at index `s`,
  -- and the forgery verifies under that challenge relative to `pk`. Pairing this across
  -- both runs gives two accepting transcripts with the same commitment and distinct
  -- challenges — exactly what special soundness needs.
  let P_out : Stmt →
      Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
        QueryLog (unifSpec + (Unit →ₒ Chal)) → Prop :=
    fun pk x log => ∀ s : Fin (qH + 1), cf x = some s →
      ∃ ω : Chal,
        QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
        x.roCache x.target = some ω ∧
        σ.verify pk x.target.2 ω x.forgery.2.2 = true
  -- Support invariant: `P_out pk` holds for every `(x, log)` in the support of the first
  -- run at public key `pk`. This follows from the definition of `Fork.runTrace`:
  -- whenever `cf x = some s` pins `x.target` to `x.queryLog[s]?` via
  -- `Fork.forkPoint_getElem?_eq_some_target`, the trace's internal RO simulation
  -- guarantees `x.roCache x.target` matches the external `Sum.inr ()` oracle response at
  -- index `s`, and the `verified` flag verifies that response against `pk`.
  have hPinv : ∀ pk x log,
      (x, log) ∈ support (replayFirstRun (wrappedMain pk)) → P_out pk x log := by
    -- TODO(p6-support-invariant): prove the support invariant by induction on
    -- `Fork.runTrace` — each counted-oracle query updates `roCache` and the
    -- external log in lockstep, so their corresponding entries match, and `verified`
    -- guarantees `σ.verify pk` succeeds at the cached challenge.
    sorry
  -- ── Step (b): per-pk forking bound via `Fork.replayForkingBound`, using the
  -- strengthened `P_out pk` to pin each run's cached challenge to its outer log entry.
  have hPerPk : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun r : Option
            (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            ∃ (x₁ x₂ :
                Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
              (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
              r = some (x₁, x₂) ∧
              cf x₁ = some s ∧
              cf x₂ = some s ∧
              QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
              P_out pk x₁ log₁ ∧
              P_out pk x₂ log₂
            | forkReplay (wrappedMain pk) qb (Sum.inr ()) cf] := by
    intro pk
    exact Fork.replayForkingBound (σ := σ) (hr := hr) (M := M) nmaAdv qH pk
      (P_out := P_out pk) (hP := fun h => hPinv pk _ _ h)
  -- ── Step (c): per-pk extraction bound. The structural fork event plus target equality
  -- (established by `hTargetEq` below) plus special soundness give witness extraction.
  -- Target equality across the two fork runs: this holds because both runs share the
  -- oracle responses up to the fork index, so the adversary's internal query-log prefix up
  -- to index `s` is identical, and `Fork.forkPoint_getElem?_eq_some_target` then
  -- forces the targets to agree.
  have hTargetEq : ∀ pk (x₁ x₂ :
      Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
      (s : Fin (qH + 1)),
      some (x₁, x₂) ∈ support (forkReplay (wrappedMain pk) qb (Sum.inr ()) cf) →
      cf x₁ = some s → cf x₂ = some s →
      x₁.target = x₂.target := by
    -- TODO(p6-target-equality): derive from `forkReplay_success_log_props` (shared prefix of
    -- `Sum.inr ()` responses up to index `s`) plus the Fork.runTrace invariant
    -- that `queryLog[n]` is determined by the first `n` counted-oracle responses.
    sorry
  have hExtract : ∀ pk : Stmt,
      Pr[ fun r : Option
          (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
            Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
          ∃ (x₁ x₂ :
              Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
            (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
            r = some (x₁, x₂) ∧
            cf x₁ = some s ∧
            cf x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
              QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
            P_out pk x₁ log₁ ∧
            P_out pk x₂ log₂
          | forkReplay (wrappedMain pk) qb (Sum.inr ()) cf] ≤
        Pr[ fun w : Wit => rel pk w = true | reduction pk] := by
    intro pk
    classical
    -- Strip the simulator from `reduction pk = simulateQ _ (forkExtract pk)`.
    rw [show Pr[fun w : Wit => rel pk w = true | reduction pk] =
          Pr[fun w : Wit => rel pk w = true | forkExtract pk] from
        probEvent_simulateQ_unifChalImpl (forkExtract pk) _]
    -- Expand `forkExtract pk` as a bind over `forkReplay` followed by the case-match
    -- extractor `branchFn`.
    set branchFn : Option
        (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
          Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) →
        OracleComp (unifSpec + (Unit →ₒ Chal)) Wit :=
      fun result => match result with
      | none => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      | some (x₁, x₂) =>
        let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
        let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
        if _hc : c₁ = c₂ then
          match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
          | some ω₁, some ω₂ =>
              if _hω : ω₁ ≠ ω₂ then
                liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + chalSpec)
              else
                liftComp ($ᵗ Wit) (unifSpec + chalSpec)
          | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        else
          liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      with hbranchFn_def
    have hforkExtract_eq :
        forkExtract pk = forkReplay (wrappedMain pk) qb (Sum.inr ()) cf >>= branchFn := rfl
    rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine ENNReal.tsum_le_tsum fun r => ?_
    -- Pointwise comparison:
    -- `(if E r then Pr[= r | mx] else 0) ≤ Pr[= r | mx] * Pr[rel | branchFn r]`.
    by_cases hE :
        ∃ (x₁ x₂ : Fork.Trace
            (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
          (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
          r = some (x₁, x₂) ∧
          cf x₁ = some s ∧
          cf x₂ = some s ∧
          QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
            QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
          P_out pk x₁ log₁ ∧
          P_out pk x₂ log₂
    swap
    · rw [if_neg hE]; exact zero_le _
    rw [if_pos hE]
    by_cases hsupp : r ∈ support (forkReplay (wrappedMain pk) qb (Sum.inr ()) cf)
    swap
    · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
    obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
    obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
    obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
    -- The two cached challenges are distinct because the outer-log entries are.
    have hω_ne : ω₁ ≠ ω₂ := by
      intro heq
      apply hneq
      rw [hlog₁, hlog₂, heq]
    -- Targets coincide by the shared-prefix property of `forkReplay`.
    have htarget : x₁.target = x₂.target :=
      hTargetEq pk x₁ x₂ s (hreq ▸ hsupp) hcf₁ hcf₂
    -- Name the projections of the forgery directly (no rcases).
    set m₁ := x₁.forgery.1 with hm₁_def
    set c₁ := x₁.forgery.2.1 with hc₁_def
    set sr₁ := x₁.forgery.2.2 with hsr₁_def
    set m₂ := x₂.forgery.1 with hm₂_def
    set c₂ := x₂.forgery.2.1 with hc₂_def
    set sr₂ := x₂.forgery.2.2 with hsr₂_def
    -- `target = (forgery.1, forgery.2.1)`, so target equality forces `m`s and `c`s.
    have htgt₁ : x₁.target = (m₁, c₁) := rfl
    have htgt₂ : x₂.target = (m₂, c₂) := rfl
    have htarget_eq : (m₁, c₁) = (m₂, c₂) := by rw [← htgt₁, ← htgt₂]; exact htarget
    have hc_eq : c₁ = c₂ := (Prod.mk.inj htarget_eq).2
    -- Specialize cache / verify to the projected form.
    have hcache₁' : x₁.roCache (m₁, c₁) = some ω₁ := hcache₁
    have hcache₂' : x₂.roCache (m₂, c₂) = some ω₂ := hcache₂
    have hverify₁' : σ.verify pk c₁ ω₁ sr₁ = true := hverify₁
    have hverify₂' : σ.verify pk c₂ ω₂ sr₂ = true := hverify₂
    have hverify₂'' : σ.verify pk c₁ ω₂ sr₂ = true := by rw [hc_eq]; exact hverify₂'
    -- Evaluate `branchFn r = liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) _`.
    have hbranch :
        branchFn r = liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec) := by
      rw [hbranchFn_def, hreq]
      change (if _hc : c₁ = c₂ then
        match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
        | some ω₁, some ω₂ =>
            if _hω : ω₁ ≠ ω₂ then
              liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec)
            else
              liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      else
        liftComp ($ᵗ Wit) (unifSpec + chalSpec)) = _
      rw [dif_pos hc_eq, hcache₁', hcache₂']
      simp only [dif_pos hω_ne]
    rw [hbranch, probEvent_liftComp]
    -- Probability on the extracted branch: 1 via special soundness + no-failure.
    have hrel_one :
        Pr[fun w : Wit => rel pk w = true | σ.extract ω₁ sr₁ ω₂ sr₂] = 1 := by
      rw [probEvent_eq_one_iff]
      refine ⟨hss_nf ω₁ sr₁ ω₂ sr₂, fun w hw => ?_⟩
      exact SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk)
        hω_ne hverify₁' hverify₂'' hw
    rw [hrel_one, mul_one]
  -- ── Step (d): integrate (b)∘(c) over keygen using Cauchy-Schwarz / Jensen.
  -- Combining (b) and (c) gives the per-pk forking bound; integrating via
  -- `jensen_keygen_forking_bound` lifts it to the expected bound.
  have hPerPkFinal : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun w : Wit => rel pk w = true | reduction pk] := fun pk =>
    (hPerPk pk).trans (hExtract pk)
  -- Rewrite the advantage as the expected acceptance over keygen (marginalized to `pk`).
  have hAdv_eq_tsum :
      Fork.advantage σ hr M nmaAdv qH =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    rw [hAdv_eq]
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rw [probOutput_liftComp]
    congr 1
    rcases pkw with ⟨pk, sk⟩
    simp only [bind_pure_comp, probEvent_map, Function.comp_def, acc]
  -- Rewrite the RHS (`Pr[= true | hardRelationExp]`) as a keygen-marginalized sum.
  have hRHS_eq_tsum : Pr[= true | hardRelationExp hr reduction] =
      ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
        Pr[ fun w : Wit => rel pkw.1 w = true | reduction pkw.1] := by
    unfold hardRelationExp
    rw [← probEvent_eq_eq_probOutput]
    simp only [bind_pure_comp, probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rcases pkw with ⟨pk, sk⟩
    congr 1
    rw [probEvent_map]
    rfl
  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  -- Instantiate `jensen_keygen_forking_bound` with the keygen distribution.
  have hinv_le : challengeSpaceInv Chal ≤ 1 := by
    unfold challengeSpaceInv
    have hcard : (1 : ENNReal) ≤ (Fintype.card Chal : ENNReal) := by
      exact_mod_cast Fintype.card_pos
    exact ENNReal.inv_le_one.2 hcard
  have hinv_ne_top : challengeSpaceInv Chal ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hinv_le
  have hacc_le : ∀ pkw : Stmt × Wit, acc pkw.1 ≤ 1 := fun _ =>
    probEvent_le_one
  exact jensen_keygen_forking_bound (gen := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true | reduction pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    hinv_ne_top hacc_le
    (fun pkw => hPerPkFinal pkw.1)
/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing `qS · ζ_zk + ζ_col`.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.

The combined bound is:

  `(ε - qS·ζ_zk - ζ_col) · ((ε - qS·ζ_zk - ζ_col) / (qH+1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`. The ENNReal subtraction truncates at zero, so
the bound is trivially satisfied when the simulation loss exceeds the advantage. -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk ζ_col : ℝ) (hζ_zk : 0 ≤ ζ_zk) (hζ_col : 0 ≤ ζ_col)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      let eps := adv.advantage (runtime M) -
        ENNReal.ofReal (qS * ζ_zk + ζ_col)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk ζ_col hζ_zk hζ_col hhvzk adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) - ENNReal.ofReal (qS * ζ_zk + ζ_col) ≤
      Fork.advantage σ hr M nmaAdv qH :=
    tsub_le_iff_left.mpr (by rwa [add_comm])
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end FiatShamir
