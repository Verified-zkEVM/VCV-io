/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.Loss
public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Projections

/-!
# EUF-CMA for Fiat-Shamir with aborts: BodyHops

The per-signing-query core of the Trans → Sim hop
(`tvDist_run_transSignBody_simSignBody_le`) and the verification-and-freshness
continuation of the hybrid experiment (`hybridVerifyCont`).

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/

public section

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

omit [SampleableType Stmt] in
/-- **Per-signing-query core of the Trans → Sim hop.** From any shared starting cache,
the accepted-only-reprogramming body and the simulated body are within total-variation
distance `ζ_zk · (1 + q + ⋯ + q^(maxAttempts-1)) ≤ ζ_zk / (1 - q)` on their joint
output-and-cache distribution, where `ζ_zk` bounds the per-attempt HVZK error and `q`
the simulator's per-attempt abort probability.

The cache programming is the same deterministic continuation on both sides
(`signProgramCont`), so the bound reduces to `tvDist_firstSome_le_geometric` on the
private restart loops. -/
lemma tvDist_run_transSignBody_simSignBody_le
    (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true) (msg : M)
    {ζ_zk : ℝ} (hhvzk : ids.HVZK sim ζ_zk)
    {q : ℝ} (hq : Pr[= none | sim pk].toReal ≤ q) (hq0 : 0 ≤ q)
    (s : (M × Commit →ₒ Chal).QueryCache) :
    tvDist (StateT.run (transSignBody ids M maxAttempts pk sk msg) s)
        (StateT.run (simSignBody M maxAttempts sim pk sk msg) s) ≤
      ζ_zk * ∑ j ∈ Finset.range maxAttempts, q ^ j := by
  have hcore : tvDist (firstSome (ids.honestExecution pk sk) maxAttempts)
      (firstSome (sim pk) maxAttempts) ≤
        ζ_zk * ∑ j ∈ Finset.range maxAttempts, q ^ j :=
    tvDist_firstSome_le_geometric (ids.honestExecution pk sk) (sim pk)
      (hhvzk pk sk hrel) hq hq0 maxAttempts
  have hrw : ∀ (loop : ProbComp (Option (Commit × Chal × Resp))),
      StateT.run (liftM loop >>= signProgramCont M msg) s =
        loop >>= fun r => StateT.run (signProgramCont M msg r) s := by
    intro loop
    simp [StateT.run_bind]
  rw [transSignBody, simSignBody, hrw, hrw]
  exact le_trans (tvDist_bind_right_le _ _ _) hcore

/-- The hybrid unforgeability experiment at a fixed key pair: run the adversary with the
base handlers and the given signing body, then verify the forgery under the final cache
and apply the freshness check. Instantiating `signBody` with `realSignBody`,
`progSignBody`, `transSignBody`, and `simSignBody` yields the games G₀ — G₃ of the
CMA-to-NMA hybrid chain. -/
@[expose] noncomputable def hybridExpAtKey
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (pk : Stmt) : ProbComp Bool := do
  let ((msg, σ), (cache, signed)) ← StateT.run
    (simulateQ
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M signBody)
      (adv.main pk)) (∅, [])
  let ok ← StateT.run'
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg σ)) cache
  pure (decide (msg ∉ signed) && ok)

/-! ## Verification tail -/

/-- Verification-and-freshness continuation of `hybridExpAtKey`, as a function of the
adversary's forgery and the final hybrid state. -/
@[expose] noncomputable def hybridVerifyCont (pk : Stmt)
    (z : (M × Option (Commit × Resp)) × ((M × Commit →ₒ Chal).QueryCache × List M)) :
    ProbComp Bool := do
  let ok ← StateT.run'
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk z.1.1 z.1.2)) z.2.1
  pure (decide (z.1.1 ∉ z.2.2) && ok)

omit [SampleableType Stmt] in
lemma hybridExpAtKey_eq_run_bind
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (pk : Stmt) :
    hybridExpAtKey ids hr M maxAttempts adv signBody pk =
      (simulateQ
          (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M signBody)
          (adv.main pk)).run (∅, []) >>=
        hybridVerifyCont ids hr M maxAttempts pk := by
  refine bind_congr fun z => ?_
  rcases z with ⟨⟨msg, σ⟩, cache, signed⟩
  rfl

omit [SampleableType Stmt] in
/-- The verification continuation only reads the cache at the forged message's points,
so it is insensitive to cache changes away from them. -/
lemma hybridVerifyCont_cache_congr (pk : Stmt) (ms : M × Option (Commit × Resp))
    (c₁ c₂ : (M × Commit →ₒ Chal).QueryCache) (l : List M)
    (h : ∀ w : Commit, c₁ (ms.1, w) = c₂ (ms.1, w)) :
    hybridVerifyCont ids hr M maxAttempts pk (ms, (c₁, l)) =
      hybridVerifyCont ids hr M maxAttempts pk (ms, (c₂, l)) := by
  rcases ms with ⟨msg, _ | ⟨w, zr⟩⟩
  · rfl
  · refine congrArg (· >>= fun ok => pure (decide (msg ∉ l) && ok)) ?_
    have hside : ∀ c : (M × Commit →ₒ Chal).QueryCache,
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          ((FiatShamirWithAbort
            (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
            ids hr M maxAttempts).verify pk msg (some (w, zr)))).run' c =
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            ids.verify pk w cu.1 zr) <$> roStep M c (msg, w) := by
      intro c
      simp only [FiatShamirWithAbort, simulateQ_bind, roSim.simulateQ_HasQuery_query,
        simulateQ_pure]
      change Prod.fst <$> (((randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) (msg, w) >>=
            fun cc => pure (ids.verify pk w cc zr)).run c) = _
      rw [StateT.run_bind]
      rw [show ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) (msg, w)).run c =
        roStep M c (msg, w) from randomOracle_run_eq_roStep M c (msg, w)]
      simp
    rw [hside c₁, hside c₂]
    cases hc : c₁ (msg, w) with
    | some v =>
        rw [roStep_of_some M hc,
          roStep_of_some M (show c₂ (msg, w) = some v from (h w).symm.trans hc)]
        simp
    | none =>
        rw [roStep_of_none M hc,
          roStep_of_none M (show c₂ (msg, w) = none from (h w).symm.trans hc)]
        simp

omit [SampleableType Stmt] in
/-- When the forged message has already been signed, the freshness conjunct forces the
game output to `false`, so the success probability vanishes regardless of the cache. -/
lemma probOutput_true_hybridVerifyCont_of_mem (pk : Stmt)
    (ms : M × Option (Commit × Resp))
    (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) (hmem : ms.1 ∈ l) :
    Pr[= true | hybridVerifyCont ids hr M maxAttempts pk (ms, (c, l))] = 0 := by
  rw [hybridVerifyCont, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun ok => ?_
  rw [probOutput_pure, if_neg (by simp [hmem]), mul_zero]

end scaffold

end EUF_CMA

end FiatShamirWithAbort
