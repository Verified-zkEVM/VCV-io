/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Chain
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.EvalDist.Inequalities

/-!
# Fiat-Shamir reductions for Sigma protocols

This file exposes the CMA-to-NMA reduction used by the public Sigma security
theorem. The current proof is discharged by the HeapSSP game chain, but callers
depend only on the reduction statement here.
-/

namespace FiatShamir

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-- CMA-to-NMA reduction for Fiat-Shamir signatures built from a Sigma protocol.

The reduction runs the CMA adversary with simulated signing transcripts and a
managed random oracle. Its quantitative loss is the HVZK simulation cost, the
programming-collision term from simulator commit predictability, and the
fresh-challenge verification slack. -/
theorem cma_to_nma_advantage_bound
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (δ_verify : ENNReal)
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β +
          δ_verify :=
  HeapSSP.cma_advantage_le_fork_bound (σ := σ) (hr := hr) (M := M)
    simTranscript ζ_zk hζ_zk hHVZK β hPredSim δ_verify hVerifyGuess adv qS qH hQ

section evalDistBridge

variable [Fintype Chal] [Inhabited Chal] [SampleableType Chal]

/-- The `ofLift + uniformSampleImpl` simulation on `unifSpec + (Unit →ₒ Chal)` preserves
`evalDist`. Both oracle components sample uniformly from their range. -/
private lemma evalDist_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) :
    evalDist (simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa) = evalDist oa := by
  apply OracleComp.evalDist_simulateQ_eq_evalDist
  intro t
  rcases t with n | u
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    rw [evalDist_query (spec := unifSpec + (Unit →ₒ Chal))]
    exact (evalDist_query (spec := unifSpec) n)
  · simp only [QueryImpl.add_apply_inr, uniformSampleImpl]
    have heq : (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
          SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
        (evalDist (liftM (query (Sum.inr u)) :
          OracleComp (unifSpec + (Unit →ₒ Chal)) _) :
          SPMF ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr u))) := by
      rw [evalDist_uniformSample, evalDist_query]; rfl
    exact heq

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

end evalDistBridge

section nmaToExtraction

variable [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]

/-- Replay-fork query budget for the NMA reduction: forward the `.inl unifSpec` component
live and rewind only the counted challenge oracle on the `.inr` side. -/
private def nmaForkBudget (qH : ℕ) : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => qH

/-- Per-run invariant for the NMA replay fork. If `Fork.forkPoint qH` selects index `s`,
the cached RO value at `x.target`, the outer log's `s`-th counted-oracle response, and the
challenge under which `x.forgery` verifies all coincide. -/
private def forkSupportInvariant
    (qH : ℕ) (pk : Stmt)
    (x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (log : QueryLog (unifSpec + (Unit →ₒ Chal))) : Prop :=
  ∀ s : Fin (qH + 1),
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x =
        some s →
    ∃ ω : Chal,
      QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
      x.roCache x.target = some ω ∧
      σ.verify pk x.target.2 ω x.forgery.2.2 = true

variable [SampleableType Wit] [SampleableType Chal] [Fintype Chal] [Inhabited Chal]

/-- Witness-extraction computation used by the NMA reduction. -/
private noncomputable def nmaForkExtract
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt) :
    OracleComp (unifSpec + (Unit →ₒ Chal)) Wit := do
  let result ← forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)
  match result with
  | none => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
  | some (x₁, x₂) =>
    let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
    let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
    if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
          if _hω : ω₁ ≠ ω₂ then
            liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + (Unit →ₒ Chal))
          else
            liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
      | _, _ => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
    else
      liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))

/-- NMA reduction for `nma_to_hard_relation_bound`: simulate the challenge oracle of
`nmaForkExtract` down to `ProbComp`. -/
private noncomputable def nmaReduction
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : Stmt → ProbComp Wit := fun pk =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))) (nmaForkExtract σ hr M nmaAdv qH pk)

omit [SampleableType Wit] [Inhabited Chal] [Fintype Chal] in
/-- Every `(x, log)` in the support of `replayFirstRun (Fork.runTrace σ hr M nmaAdv pk)`
satisfies the per-run invariant `forkSupportInvariant`. -/
private theorem forkSupportInvariant_of_mem_replayFirstRun
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {log : QueryLog (unifSpec + (Unit →ₒ Chal))}
    (h : (x, log) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    forkSupportInvariant σ M qH pk x log := by
  classical
  intro s hs
  have htarget : x.queryLog[(↑s : ℕ)]? = some x.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hverified : x.verified = true :=
    Fork.forkPoint_some_imp_verified (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hslt : (↑s : ℕ) < x.queryLog.length := by
    by_contra hge
    push Not at hge
    have hnone : x.queryLog[(↑s : ℕ)]? = none := List.getElem?_eq_none hge
    rw [hnone] at htarget
    exact (Option.some_ne_none x.target htarget.symm).elim
  obtain ⟨ω, hcache_idx, hlog⟩ :=
    Fork.runTrace_cache_outer_lockstep σ hr M nmaAdv pk h (↑s : ℕ) hslt
  have htgt_eq : x.queryLog[(↑s : ℕ)]'hslt = x.target := by
    have h1 : x.queryLog[(↑s : ℕ)]? = some (x.queryLog[(↑s : ℕ)]'hslt) :=
      List.getElem?_eq_getElem hslt
    rw [h1] at htarget
    exact Option.some.inj htarget
  rw [htgt_eq] at hcache_idx
  obtain ⟨ω', hcache', hverify⟩ :=
    Fork.runTrace_verified_imp_verify σ hr M nmaAdv pk h hverified
  have hωeq : ω = ω' := by
    rw [hcache_idx] at hcache'
    exact Option.some.inj hcache'
  refine ⟨ω, hlog, hcache_idx, ?_⟩
  rw [hωeq]
  exact hverify

/-- Given the structural forking event on `pk`, the NMA reduction recovers a valid witness
with probability at least that of the fork event under `forkReplay`. -/
private theorem perPk_extraction_bound
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    (pk : Stmt) :
    Pr[ fun r : Option
        (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
          Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
        ∃ (x₁ x₂ :
            Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
          (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
          r = some (x₁, x₂) ∧
          Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH x₁ = some s ∧
          Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH x₂ = some s ∧
          QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
            QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
          forkSupportInvariant σ M qH pk x₁ log₁ ∧
          forkSupportInvariant σ M qH pk x₂ log₂
        | forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
          (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH)] ≤
      Pr[ fun w : Wit => rel pk w = true | nmaReduction σ hr M nmaAdv qH pk] := by
  classical
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  let wrappedMain : OracleComp (unifSpec + chalSpec)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    Fork.runTrace σ hr M nmaAdv pk
  let cf : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      Option (Fin (qH + 1)) :=
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  let qb : ℕ ⊕ Unit → ℕ := nmaForkBudget qH
  rw [show Pr[fun w : Wit => rel pk w = true | nmaReduction σ hr M nmaAdv qH pk] =
        Pr[fun w : Wit => rel pk w = true | nmaForkExtract σ hr M nmaAdv qH pk] by
      unfold nmaReduction
      exact probEvent_simulateQ_unifChalImpl _ _]
  set branchFn : Option
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
        Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) →
      OracleComp (unifSpec + chalSpec) Wit :=
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
      nmaForkExtract σ hr M nmaAdv qH pk =
        forkReplay wrappedMain qb (Sum.inr ()) cf >>= branchFn := by
    unfold nmaForkExtract
    rfl
  rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  by_cases hE :
      ∃ (x₁ x₂ : Fork.Trace
          (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
        (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
        r = some (x₁, x₂) ∧
        cf x₁ = some s ∧
        cf x₂ = some s ∧
        QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
          QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
        forkSupportInvariant σ M qH pk x₁ log₁ ∧
        forkSupportInvariant σ M qH pk x₂ log₂
  swap
  · rw [if_neg hE]; exact zero_le _
  rw [if_pos hE]
  by_cases hsupp : r ∈ support (forkReplay wrappedMain qb (Sum.inr ()) cf)
  swap
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
  obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
  obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
  obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
  have hω_ne : ω₁ ≠ ω₂ := by
    intro heq
    apply hneq
    rw [hlog₁, hlog₂, heq]
  have htarget : x₁.target = x₂.target :=
    Fork.runTrace_target_eq_of_mem_forkReplay σ hr M nmaAdv qH pk x₁ x₂ s
      (hreq ▸ hsupp) hcf₁ hcf₂
  set m₁ := x₁.forgery.1
  set c₁ := x₁.forgery.2.1
  set sr₁ := x₁.forgery.2.2
  set m₂ := x₂.forgery.1
  set c₂ := x₂.forgery.2.1
  set sr₂ := x₂.forgery.2.2
  have htgt₁ : x₁.target = (m₁, c₁) := rfl
  have htgt₂ : x₂.target = (m₂, c₂) := rfl
  have htarget_eq : (m₁, c₁) = (m₂, c₂) := by rw [← htgt₁, ← htgt₂]; exact htarget
  have hc_eq : c₁ = c₂ := (Prod.mk.inj htarget_eq).2
  have hcache₁' : x₁.roCache (m₁, c₁) = some ω₁ := hcache₁
  have hcache₂' : x₂.roCache (m₂, c₂) = some ω₂ := hcache₂
  have hverify₁' : σ.verify pk c₁ ω₁ sr₁ = true := hverify₁
  have hverify₂' : σ.verify pk c₂ ω₂ sr₂ = true := hverify₂
  have hverify₂'' : σ.verify pk c₁ ω₂ sr₂ = true := by rw [hc_eq]; exact hverify₂'
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
  have hrel_one :
      Pr[fun w : Wit => rel pk w = true | σ.extract ω₁ sr₁ ω₂ sr₂] = 1 := by
    rw [probEvent_eq_one_iff]
    refine ⟨hss_nf ω₁ sr₁ ω₂ sr₂, fun w hw => ?_⟩
    exact SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk)
      hω_ne hverify₁' hverify₂'' hw
  rw [hrel_one, mul_one]

end nmaToExtraction

/-- NMA-to-extraction via the forking lemma and special soundness. -/
theorem nma_to_hard_relation_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Wit] [SampleableType Chal]
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
  haveI : DecidableEq Chal := Classical.decEq Chal
  refine ⟨nmaReduction σ hr M nmaAdv qH, ?_⟩
  set acc : Stmt → ENNReal := fun pk =>
    Pr[ fun x => (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH x).isSome | Fork.runTrace σ hr M nmaAdv pk] with hacc_def
  have hAdv_eq_tsum :
      Fork.advantage σ hr M nmaAdv qH =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    change Pr[= true | Fork.exp σ hr M nmaAdv qH] = _
    unfold Fork.exp
    simp only [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl,
      probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def,
      probEvent_liftComp, acc]
  have hRHS_eq_tsum :
      Pr[= true | hardRelationExp hr (nmaReduction σ hr M nmaAdv qH)] =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
          Pr[ fun w : Wit => rel pkw.1 w = true |
            nmaReduction σ hr M nmaAdv qH pkw.1] := by
    unfold hardRelationExp
    simp only [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_bind_eq_tsum,
      probEvent_map, Function.comp_def]
  have hPerPk : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun r : Option
            (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            ∃ (x₁ x₂ :
                Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
              (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
              r = some (x₁, x₂) ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH x₁ = some s ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH x₂ = some s ∧
              QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
              forkSupportInvariant σ M qH pk x₁ log₁ ∧
              forkSupportInvariant σ M qH pk x₂ log₂
            | forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
              (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH)] := fun pk =>
    Fork.replayForkingBound (σ := σ) (hr := hr) (M := M) nmaAdv qH pk
      (P_out := forkSupportInvariant σ M qH pk)
      (hP := fun h => forkSupportInvariant_of_mem_replayFirstRun σ hr M nmaAdv qH pk h)
      (hreach := Fork.runTrace_forkPoint_CfReachable
        (σ := σ) (hr := hr) (M := M) nmaAdv qH pk)
  have hPerPkFinal : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun w : Wit => rel pk w = true |
          nmaReduction σ hr M nmaAdv qH pk] := fun pk =>
    (hPerPk pk).trans (perPk_extraction_bound σ hr M nmaAdv qH hss hss_nf pk)
  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  have hinv_le : challengeSpaceInv Chal ≤ 1 := by
    unfold challengeSpaceInv
    have hcard : (1 : ENNReal) ≤ (Fintype.card Chal : ENNReal) := by
      exact_mod_cast Fintype.card_pos
    exact ENNReal.inv_le_one.2 hcard
  have hinv_ne_top : challengeSpaceInv Chal ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hinv_le
  exact OracleComp.EvalDist.marginalized_jensen_forking_bound (mx := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true |
      nmaReduction σ hr M nmaAdv qH pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    hinv_ne_top (fun _ => probEvent_le_one) (fun pkw => hPerPkFinal pkw.1)

end FiatShamir
