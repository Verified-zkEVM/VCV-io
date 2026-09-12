/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.NMAReduction

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
following Theorem 3 of Barbosa et al. (CRYPTO 2023, ePrint 2023/246).
Instantiates `FiatShamir.signHashQueryBound` at the with-aborts signature type
and exposes `cmaToNmaLoss` plus `euf_cma_to_nma` (the managed-RO NMA interface),
together with the hybrid game chain (`hybridExpAtKey` over the signing bodies
`realSignBody`, `progSignBody`, `transSignBody`, `simSignBody`) that structures
the proof.

The quantitative parameters `ε` (per-key commitment-guessing probability),
`p_abort` (per-attempt abort probability), and `δ` (key-regularity failure
probability) are tied to the identification scheme by explicit hypotheses on a
"good key" event, mirroring the event `Γ` of the paper's Lemma 1: `δ` bounds
the probability that key generation falls outside the event, and `ε`/`p_abort`
bound the per-key quantities pointwise on it.

The scheme-specific NMA-to-hard-problem reduction lives with each concrete
scheme (e.g. `MLDSA.nma_security_short`).

## Module layout

The development is split along its proof phases, each module publicly
importing its predecessor: `Loss` (the loss functions), `BodyHops` (the
per-query Trans → Sim hop core and the verification tail), `GhostReadCharge`,
`HiddenReadFold`, `CouplingEngine` (reusable measure-level coupling
infrastructure, off the live path), `ReadRecording`, `TapeFactorization`,
`HopLemmas`, and `NMAReduction`. This module closes the chain: the bridge from
the managed-RO NMA experiment to the plain EUF-NMA interface (Option B: the
forgery's own verification point is discarded from the returned cache), and
the assembled headline `euf_cma_to_nma`.
-/

@[expose] public section

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

/-! ## Bridge to the plain EUF-NMA interface

Option B makes `simulatedNmaAdv` discard the forgery's own verification point from the
returned managed cache. The single hash query issued by `FiatShamirWithAbort.verify`
therefore always *misses* in the overlay and falls through to the live oracle, so the
overlay verification coincides — as an `OracleComp` — with the plain verification. This
collapses the managed-RO NMA experiment onto the plain EUF-NMA experiment of the
cache-forgetting adversary `simulatedEufNmaAdv`, making the bound
`Pr[managedRoNmaExp simulatedNmaAdv] ≤ simulatedEufNmaAdv.advantage` sound. -/

/-- The plain EUF-NMA adversary underlying `simulatedNmaAdv`: run the same managed
simulation of the CMA adversary, but forget the returned cache and verify in the plain
random-oracle model. By Option B (`withCacheOverlay_verify_eq_of_miss`) the managed-RO NMA
experiment of `simulatedNmaAdv` coincides with the plain EUF-NMA experiment of this
adversary. -/
noncomputable def simulatedEufNmaAdv :
    SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts) where
  main pk := Prod.fst <$> (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk

omit [SampleableType Stmt] in
/-- **Soundness of the managed-RO → plain EUF-NMA bridge** (Option B). The managed-RO NMA
success probability of `simulatedNmaAdv` equals the plain EUF-NMA success probability of
`simulatedEufNmaAdv`. The Option B post-processing erases the forgery's own verification
point from the returned cache, so `withCacheOverlay` agrees with the plain live verifier
on every forgery (`withCacheOverlay_verify_eq_of_miss`); in particular a replayed signed
forgery no longer wins through a programmed challenge. -/
lemma managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp :
    SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv) =
      SignatureAlg.eufNmaExp (runtime M)
        (simulatedEufNmaAdv ids hr M maxAttempts sim adv) := by
  unfold SignatureAlg.managedRoNmaExp SignatureAlg.eufNmaExp
  refine congrArg (runtime M).evalSPMF ?_
  refine bind_congr fun pksk => ?_
  -- Reduce the eufNma side `Prod.fst <$> _` to a bind, so both sides bind over
  -- `simulatedNmaAdv.main`, then compare the verification wrappers pointwise.
  change ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1 >>= fun result =>
      withCacheOverlay result.2
        ((FiatShamirWithAbort ids hr M maxAttempts).verify
          pksk.1 result.1.1 result.1.2)) =
    (Prod.fst <$> (simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1) >>= fun ms =>
      (FiatShamirWithAbort ids hr M maxAttempts).verify pksk.1 ms.1 ms.2
  rw [map_eq_bind_pure_comp, bind_assoc]
  -- Unfold `.main` to expose the inner managed run followed by the Option-B
  -- post-processing, then `bind_congr` over the inner run.
  simp only [simulatedNmaAdv, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun r => ?_
  -- `r.1.2` is the inner forgery's signature; the post-processed cache erases its own
  -- verification point, so the overlay verification agrees with the plain verification.
  refine withCacheOverlay_verify_eq_of_miss ids hr M maxAttempts _ pksk.1 r.1.1 r.1.2 ?_
  intro w' z hσ
  simp only [hσ, Function.update_self]

/-! ## Assembly -/

omit [SampleableType Stmt] in
/-- **CMA-to-NMA reduction for Fiat-Shamir with aborts** (after Theorem 3, CRYPTO 2023),
at the managed-RO NMA interface: for any EUF-CMA adversary making at most `qS` signing
and `qH` hash queries, the CMA advantage is bounded by the managed-RO NMA success
probability of `simulatedNmaAdv` plus the statistical loss `cmaToNmaLoss`.

The good-key event `Good` plays the role of the event `Γ` in the paper's Lemma 1: `δ`
bounds its complement under key generation, while `ε` and `p_abort` bound the per-key
commitment-guessing and per-attempt abort probabilities pointwise on it. The pointwise form
of `hGuess` on good keys is stronger than the key-averaged commitment-guessing condition of
ePrint 2023/246; it is conservative and therefore sound, and the averaged form would matter
only for tightness, not soundness. -/
theorem euf_cma_to_nma
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk) (hhvzk : ids.HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : Stmt → Wit → Prop)
    (hGood : Pr[ fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] ≤ ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    adv.advantage (runtime M) ≤
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] +
      ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  -- `advantage = Pr[G₀]` via the per-key bridge `G₀`.
  rw [SignatureAlg.unforgeableAdv.advantage,
    probOutput_unforgeableExp_eq_hybridExpAtKey_real ids hr M maxAttempts adv]
  -- Nonnegativity of the three per-hop slack pieces.
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hA : 0 ≤ qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) + qS * (qH + 1) * ε / (1 - p_abort) :=
    add_nonneg
      (div_nonneg (by positivity) (by positivity))
      (div_nonneg (by positivity) (le_of_lt h1p))
  have hB : 0 ≤ qS * (qH + 1) * ε / (1 - p_abort) := div_nonneg (by positivity) (le_of_lt h1p)
  have hC : 0 ≤ qS * ζ_zk / (1 - p_abort) := div_nonneg (by positivity) (le_of_lt h1p)
  have hPK : 0 ≤ perKeyLoss qS qH ε p_abort ζ_zk := by unfold perKeyLoss; positivity
  -- Per-key chain on good keys: `real ≤ sim + ofReal (perKeyLoss)`.
  have hperkey : ∀ x ∈ support hr.gen, Good x.1 x.2 →
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
        Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim x.1 x.2) x.1] +
        ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
    rintro ⟨pk, sk⟩ hmem hgood
    have hrel : rel pk sk = true := hr.gen_sound pk sk hmem
    have step1 := probOutput_hybridExpAtKey_real_le_prog ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hQ pk sk (hGuess pk sk hgood) (hAbort pk sk hgood)
    have step2 := probOutput_hybridExpAtKey_prog_le_trans ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hε hQ pk sk (hGuess pk sk hgood) (hAbort pk sk hgood)
    have step3 := probOutput_hybridExpAtKey_trans_le_sim ids hr M maxAttempts sim adv ζ_zk hζ hhvzk
      qS qH p_abort hp₀ hp hQ pk sk hrel (hAbortSim pk sk hgood)
    -- Chain the three hops and collapse the `ofReal` sums (slack pieces nonneg).
    calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts pk sk) pk]
        ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (fun x ↦ progSignBody ids M pk sk x maxAttempts) pk] +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := step1
      _ ≤ (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (transSignBody ids M maxAttempts pk sk) pk] +
            ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort))) +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := by gcongr
      _ ≤ ((Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim pk sk) pk] +
            ENNReal.ofReal (qS * ζ_zk / (1 - p_abort))) +
            ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort))) +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := by gcongr
      _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim pk sk) pk] +
            ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
          have hcollapse :
              ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) +
                ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) +
                ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
                  qS * (qH + 1) * ε / (1 - p_abort)) =
                ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
            rw [← ENNReal.ofReal_add hC hB, ← ENNReal.ofReal_add (add_nonneg hC hB) hA]
            congr 1
            unfold perKeyLoss
            ring
          rw [add_assoc, add_assoc, ← add_assoc (ENNReal.ofReal (qS * ζ_zk / (1 - p_abort))),
            hcollapse]
  -- Average the per-key bound over `hr.gen`, paying `δ` on the complement of `Good`.
  have hbound : Pr[= true | do
        let x ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
      Pr[= true | do
        let x ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim x.1 x.2) x.1] +
        ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) + ENNReal.ofReal δ := by
    simp only [probOutput_bind_eq_tsum]
    -- Pointwise: split on `Good`. On `Good` use `hperkey`; off `Good` charge the `δ` slot.
    have hpt : ∀ x : Stmt × Wit,
        Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
          Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (simSignBody M maxAttempts sim x.1 x.2) x.1] +
          Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) +
          Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0) := by
      intro x
      by_cases hx : x ∈ support hr.gen
      · by_cases hg : Good x.1 x.2
        · have := mul_le_mul' (le_refl (Pr[= x | hr.gen])) (hperkey x hx hg)
          calc Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (realSignBody ids M maxAttempts x.1 x.2) x.1]
              ≤ Pr[= x | hr.gen] *
                  (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                    (simSignBody M maxAttempts sim x.1 x.2) x.1] +
                  ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk)) := this
            _ = Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (simSignBody M maxAttempts sim x.1 x.2) x.1] +
                Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) :=
                mul_add ..
            _ ≤ _ := by simp [hg]
        · -- Off `Good`: real ≤ 1, charged to the indicator slot.
          have : Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
              Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0) := by
            simp only [hg, not_false_eq_true, if_true]
            exact mul_le_mul' le_rfl probOutput_le_one
          exact le_trans this le_add_self
      · simp [probOutput_eq_zero_of_not_mem_support hx]
    calc ∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts x.1 x.2) x.1]
        ≤ ∑' x, (Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1] +
            Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) +
            Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)) :=
          ENNReal.tsum_le_tsum hpt
      _ = (∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1]) +
            (∑' x, Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk)) +
            (∑' x, Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
      _ ≤ (∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1]) +
            ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) + ENNReal.ofReal δ := by
          gcongr
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
          · calc ∑' x, Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)
                = ∑' x, if ¬ Good x.1 x.2 then Pr[= x | hr.gen] else 0 := by
                  refine tsum_congr fun x => ?_; by_cases hg : Good x.1 x.2 <;> simp [hg]
              _ = Pr[fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] := by
                  rw [probEvent_eq_tsum_ite]
              _ ≤ ENNReal.ofReal δ := hGood
  -- Final: glue with the NMA bridge and reassociate the loss.
  refine le_trans hbound ?_
  rw [cmaToNmaLoss_eq_perKeyLoss_add, ENNReal.ofReal_add hPK hδ, add_assoc]
  gcongr
  exact probOutput_hybridExp_sim_le_managedRoNmaExp ids hr M maxAttempts sim adv

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Cache-invariant companion to `simulatedNmaAdv`: the reduction issues at most `qH`
live hash queries (the signing simulation samples transcripts using only uniform
queries and programs the managed cache). Mirrors
`FiatShamir.simulatedNmaAdv_hashQueryBound` from the Σ-protocol track. -/
lemma simulatedNmaAdv_nmaHashQueryBound
    [Finite Chal] [Inhabited Chal]
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∀ pk, FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk) qH := by
  have : Fintype Chal := Fintype.ofFinite Chal
  let : IsUniformSpec ((M × Commit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  intro pk
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
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
    let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
    match r with
    | some (w, c, z) =>
        modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
    | none => pure none
  -- Step bound for `fwd`: 0 live hash queries on `.inl`, exactly 1 on `.inr`.
  have hfwd :
      ∀ (t : spec.Domain) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (fwd t).run s) (match t with
            | .inl _ => 0
            | .inr _ => 1) := by
    intro t s
    cases t with
    | inl n =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inl n))) 0 by
                exact (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit)
                  (Chal := Chal) (.inl n) 0).2 trivial)
            (fun u =>
              show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
    | inr mc =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inr mc))) 1 by
                exact (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit)
                  (Chal := Chal) (.inr mc) 1).2 (Nat.succ_pos 0))
            (fun u =>
              show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
  -- Step bound for `roSim`: a cache hit issues no live query, a miss issues exactly one.
  have hro :
      ∀ (mc : M × Commit) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (roSim mc).run s) 1 := by
    intro mc s
    cases hs : s (.inr mc) with
    | some v =>
        simp [roSim, hs, FiatShamir.nmaHashQueryBound]
    | none =>
        simp only [FiatShamir.nmaHashQueryBound, Sum.forall, Prod.forall, StateT.run_bind,
          StateT.run_get, pure_bind, hs, StateT.run_modifyGet, bind_pure_comp,
          isQueryBoundP_map_iff, roSim] at ⊢ hfwd
        exact hfwd.2 mc.1 mc.2 s
  -- Step bound for `sigSim`: the simulator loop samples under `unifSim` (uniform-only)
  -- and then programs the managed cache, issuing no live hash query.
  have hsig :
      ∀ (msg : M) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (sigSim msg).run s) 0 := by
    intro msg s
    have htranscript :
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (simulateQ unifSim (firstSome (sim pk) maxAttempts)).run s) 0 := by
      unfold FiatShamir.nmaHashQueryBound
      refine OracleComp.IsQueryBoundP.simulateQ_run_of_step
        (p := fun _ : ℕ => False) (impl := unifSim)
        (oa := firstSome (sim pk) maxAttempts)
        (OracleComp.isQueryBoundP_false _ _)
        (fun _ h _ => h.elim)
        ?_ s
      intro n _ s'
      have h := hfwd (.inl n) s'
      unfold FiatShamir.nmaHashQueryBound at h
      exact h
    have hcont : ∀ (rs : Option (Commit × Chal × Resp) × spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := StateT.run
            (match rs.1 with
              | some (w, c, z) => modifyGet fun cache =>
                  (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
              | none =>
                  (pure none : StateT spec.QueryCache (OracleComp spec)
                    (Option (Commit × Resp)))) rs.2) 0 := by
      rintro ⟨(_ | ⟨w, c, z⟩), cache⟩ <;>
        simp [FiatShamir.nmaHashQueryBound, StateT.run_modifyGet]
    have hbind := FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit)
      (Chal := Chal) htranscript (fun rs => hcont rs)
    simpa [sigSim, StateT.run_bind] using hbind
  -- The run-level managed simulation issues at most `qH` live hash queries; the final
  -- pure post-processing (erasing the forgery's own verification point from the returned
  -- cache, Option B) issues none, so the total bound is `qH + 0 = qH`.
  have hrun : FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅) qH := by
    unfold FiatShamir.nmaHashQueryBound
    refine OracleComp.IsQueryBoundP.simulateQ_run_of_step (hQ pk).2 ?_ ?_ ∅
    · rintro ((n | mc) | msg) hp s'
      · simp at hp
      · exact hro mc s'
      · simp at hp
    · rintro ((n | mc) | msg) hnp s'
      · have h := hfwd (.inl n) s'
        unfold FiatShamir.nmaHashQueryBound at h
        exact h
      · simp at hnp
      · exact hsig msg s'
  have hpost : ∀ result : (M × Option (Commit × Resp)) × spec.QueryCache,
      FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := (pure ((result.1.1, result.1.2),
          match result.1.2 with
          | some (w', _) => Function.update result.2 (Sum.inr (result.1.1, w')) none
          | none => result.2) :
          OracleComp spec ((M × Option (Commit × Resp)) × spec.QueryCache))) 0 := by
    intro result
    simp [FiatShamir.nmaHashQueryBound]
  have hbind := FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit)
    (Chal := Chal) hrun (fun result => hpost result)
  change FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
    (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅ >>= fun result =>
      pure ((result.1.1, result.1.2),
        match result.1.2 with
        | some (w', _) => Function.update result.2 (Sum.inr (result.1.1, w')) none
        | none => result.2)) qH
  exact hbind

end scaffold

end EUF_CMA

end FiatShamirWithAbort
