/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.SecurityNMA

/-!
# ML-DSA short-model CMA headline: joint hypothesis-consistency witness

`MLDSA.euf_cma_security_of_nma_short` is a conditional theorem.  Its hypothesis frontier bundles
the hardness-problem pins (`hGen`, `hStmsis`), the HVZK simulator data (`sim`, `ζ_zk`, `hζ`,
`hhvzk`), the good-key package (`Good`, `hGood`, `hGuess`, `hAbort`, `hAbortSim` at some
`p_abort < 1`), the query bounds (`qS`, `qH`, `hQ`) on a CMA adversary, and the MLWE bridge
(`εbridge`, `hMlweBridge`).  A conditional theorem asserts nothing if its hypotheses are jointly
uninhabitable; this file rules that out by discharging every hypothesis **simultaneously**, at
arbitrary parameters `(p, prims)` under the same carrier instances the headline itself assumes,
and applying the headline end to end to a concrete trivial adversary
(`trivial_euf_cma_security_of_nma_short`).

This is a **logical consistency (inhabitance) witness only**: the trivial budgets (`ε = 1`,
`ζ_zk = 1`, `δ = 1`, `εbridge = 1` via `expandAIdealization` at the vacuous bound `εA = 1`), the
no-query forger, and the never-aborting simulator carry no quantitative security content, and no
security claim about any real ML-DSA parameter set follows from it.

The witness values are:

* `hr := hrShort`, `hGen := rfl` — the genuine short-key generable relation
  (`keygenShort_generable`);
* `stmsis := mldsaSTMSISShort`, `hStmsis := rfl` — the pinned SelfTargetMSIS problem;
* `sim := neverAbortSim` (constant non-`none` transcript) with `ζ_zk = 1`, discharged by
  `tvDist_le_one`;
* `Good := honestNoAbortGood` — the pairs at which the honest prover never aborts — with
  `p_abort = 0`: `hAbort` holds by definition of the event and `hAbortSim` because the simulator
  never aborts; `hGood` holds at the trivial regularity budget `δ = 1`.  Whether
  `honestNoAbortGood` is satisfiable at a given parameter set is a quantitative completeness
  question (cf. `idsWithAbort_complete`) that the frontier does not require;
* `ε = 1` for the commitment-guessing bound (`probOutput_le_one`);
* the trivial forger `trivialForger` (no queries, immediately returned `none` forgery) with
  `qS = qH = 0`;
* `mlwe := mldsaMatrixMLWE`, `εbridge = 1`: the proven seed-to-matrix reduction
  `advantage_mldsaMLWEShort_le_matrix` under `expandAIdealization p prims 1`, which holds
  unconditionally (`expandAIdealization_one`) since advantages are differences of probabilities.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

open NMA

section ShortCMAWitness

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]
  (M : Type) [DecidableEq M] [Inhabited M] [DecidableEq (Commitment p prims)]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
  [SampleableType (CommitHashBytes p)]
  [SampleableType (PublicKey p prims)]

/-! ## The witness data: simulator, good event, and trivial adversary -/

/-- The never-aborting HVZK simulator: output the default transcript with probability one.  It
discharges `hAbortSim` at `p_abort = 0` (`probOutput_none_neverAbortSim`) and the HVZK hypothesis
at the trivial budget `ζ_zk = 1` (`neverAbortSim_hvzk`); it carries no zero-knowledge content. -/
noncomputable def neverAbortSim :
    PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)) :=
  fun _ => pure (some default)

/-- The good-key event of the witness: the pairs at which the honest prover never aborts.  This
is the intended semantics of the `Good` gate in the CMA-to-NMA reduction; `hAbort` at
`p_abort = 0` holds definitionally on this event, and `hGood` holds at the trivial regularity
budget `δ = 1`.  The frontier does not require the event to be satisfiable; establishing that at
a concrete parameter set is a quantitative completeness fact, not a consistency one. -/
def honestNoAbortGood : PublicKey p prims → SecretKey p → Prop :=
  fun pk sk =>
    Pr[= none | (identificationSchemeShort p prims).honestExecution pk sk] = 0

/-- The trivial CMA forger against the short-model Fiat-Shamir-with-aborts scheme: make no
oracle queries and immediately return the aborted forgery `(default, none)`.  It witnesses the
query-bound hypothesis at `qS = qH = 0` (`trivialForger_signHashQueryBound`). -/
noncomputable def trivialForger (maxAttempts : ℕ) :
    SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)))
        (identificationSchemeShort p prims) (hrShort p prims) M maxAttempts) where
  main := fun _ => pure (default, none)

/-! ## Per-hypothesis discharges -/

omit [DecidableEq (Commitment p prims)]
  [SampleableType (PublicKey p prims)] in
/-- `hhvzk` at the trivial budget: any simulator is a `ζ_zk = 1` HVZK simulator, since total
variation distance never exceeds one. -/
lemma neverAbortSim_hvzk :
    (identificationSchemeShort p prims).HVZK (neverAbortSim p prims) 1 :=
  fun _ _ _ => tvDist_le_one _ _

omit nttOps [DecidableEq prims.High] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] [SampleableType (PublicKey p prims)] in
/-- The never-aborting simulator indeed never aborts: the probability of `none` is zero. -/
lemma probOutput_none_neverAbortSim (pk : PublicKey p prims) :
    Pr[= none | neverAbortSim p prims pk] = 0 :=
  probOutput_eq_zero_of_not_mem_support (by simp [neverAbortSim, support_pure])

omit [DecidableEq M] [DecidableEq (Commitment p prims)] [Inhabited (Commitment p prims)]
  [Inhabited (Response p prims)]
  [SampleableType (CommitHashBytes p)] [SampleableType (PublicKey p prims)] in
/-- The trivial forger makes no signing and no random-oracle queries. -/
lemma trivialForger_signHashQueryBound (maxAttempts : ℕ) (pk : PublicKey p prims) :
    FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims))
      (oa := (trivialForger p prims M maxAttempts).main pk) 0 0 :=
  ⟨isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _⟩

omit nttOps [DecidableEq prims.High] [DecidableEq (Commitment p prims)]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
  [SampleableType (CommitHashBytes p)]
  [SampleableType (PublicKey p prims)] in
/-- `expandAIdealization` holds unconditionally at the trivial budget `εA = 1`: the two branch
probabilities both lie in `[0, 1]`, so their difference is at most one in absolute value.  This
carries no idealization content; it exists to discharge the MLWE bridge of the consistency
witness through the proven reduction `advantage_mldsaMLWEShort_le_matrix`. -/
lemma expandAIdealization_one : expandAIdealization p prims 1 := by
  intro _ D
  have key : ∀ x y : ProbComp Bool,
      |(Pr[= true | x]).toReal - (Pr[= true | y]).toReal| ≤ 1 := fun x y => by
    have hx1 : (Pr[= true | x]).toReal ≤ 1 :=
      le_trans (ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one)
        (le_of_eq ENNReal.toReal_one)
    have hy1 : (Pr[= true | y]).toReal ≤ 1 :=
      le_trans (ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one)
        (le_of_eq ENNReal.toReal_one)
    have hx0 : (0 : ℝ) ≤ (Pr[= true | x]).toReal := ENNReal.toReal_nonneg
    have hy0 : (0 : ℝ) ≤ (Pr[= true | y]).toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  exact key _ _

/-! ## The joint frontier certificate -/

open scoped Classical in
omit [SampleableType (PublicKey p prims)] in
/-- **Joint consistency (inhabitance) witness for the `MLDSA.euf_cma_security_of_nma_short`
hypotheses.**  At arbitrary parameters `(p, prims)` (under the headline's own carrier
instances), any message type `M`, and any retry budget, every explicit hypothesis of the
short-model CMA headline holds simultaneously at the witness values listed in the module
docstring: the pinned generable relation and SelfTargetMSIS problem (`hGen`/`hStmsis`), the
HVZK package at `ζ_zk = 1`, the nonnegativity side conditions with `p_abort = 0 < 1`, the
good-key package (`hGood` at `δ = 1`, `hGuess` at `ε = 1`, `hAbort`/`hAbortSim` at
`p_abort = 0`), the query bounds `qS = qH = 0` on the trivial forger, and the MLWE bridge at
`εbridge = 1` through the proven seed-to-matrix reduction.  The hypothesis conjunction of the
headline is therefore jointly inhabitable; this witness carries no quantitative security
content. -/
theorem mldsa_short_cma_hyps_inhabited (maxAttempts : ℕ) :
    -- hGen
    (hrShort p prims).gen = keygenShort p prims ∧
    -- hStmsis (the pinned SelfTargetMSIS problem)
    mldsaSTMSISShort p prims M = mldsaSTMSISShort p prims M ∧
    -- hζ and hhvzk at ζ_zk = 1
    ((0 : ℝ) ≤ 1 ∧ (identificationSchemeShort p prims).HVZK (neverAbortSim p prims) 1) ∧
    -- hε, hδ, hp₀, hp at ε = 1, δ = 1, p_abort = 0
    ((0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < 1) ∧
    -- hGood at δ = 1
    (Pr[ fun xw : PublicKey p prims × SecretKey p =>
        ¬ honestNoAbortGood p prims xw.1 xw.2 | (hrShort p prims).gen] ≤
      ENNReal.ofReal 1) ∧
    -- hGuess at ε = 1
    (∀ pk sk, honestNoAbortGood p prims pk sk → ∀ cm : Commitment p prims,
      Pr[= cm | Prod.fst <$> (identificationSchemeShort p prims).commit pk sk] ≤
        ENNReal.ofReal 1) ∧
    -- hAbort at p_abort = 0
    (∀ pk sk, honestNoAbortGood p prims pk sk →
      Pr[= none | (identificationSchemeShort p prims).honestExecution pk sk] ≤
        ENNReal.ofReal 0) ∧
    -- hAbortSim at p_abort = 0
    (∀ pk sk, honestNoAbortGood p prims pk sk →
      Pr[= none | neverAbortSim p prims pk] ≤ ENNReal.ofReal 0) ∧
    -- hQ at qS = qH = 0
    (∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims))
      (oa := (trivialForger p prims M maxAttempts).main pk) 0 0) ∧
    -- hMlweBridge at mlwe = mldsaMatrixMLWE p, εbridge = 1
    (∀ main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims)),
      ∃ B : LearningWithErrors.Adversary (mldsaMatrixMLWE p),
        LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims (hrShort p prims) maxAttempts main) ≤
          LearningWithErrors.advantage (mldsaMatrixMLWE p) B + 1) :=
  ⟨rfl, rfl, ⟨zero_le_one, neverAbortSim_hvzk p prims⟩,
    ⟨zero_le_one, zero_le_one, le_rfl, zero_lt_one⟩,
    by rw [ENNReal.ofReal_one]; exact probEvent_le_one,
    fun _pk _sk _h _cm => by rw [ENNReal.ofReal_one]; exact probOutput_le_one,
    fun _pk _sk h => by rw [ENNReal.ofReal_zero]; exact h.le,
    fun pk _sk _h => by
      rw [ENNReal.ofReal_zero]; exact (probOutput_none_neverAbortSim p prims pk).le,
    trivialForger_signHashQueryBound p prims M maxAttempts,
    fun main =>
      ⟨matrixLift p prims (distinguisherBShort p prims (hrShort p prims) maxAttempts main),
        advantage_mldsaMLWEShort_le_matrix p prims (expandAIdealization_one p prims) _⟩⟩

open scoped Classical in
/-- **End-to-end applicability of the short-model CMA headline.**  The derived theorem
`MLDSA.euf_cma_security_of_nma_short` applies to the trivial forger with every hypothesis
discharged at the witness values of `mldsa_short_cma_hyps_inhabited`, producing its reductions
and bound.  Consistency-only: with `ε = ζ_zk = δ = εbridge = 1` the resulting bound is trivial,
and no quantitative claim about any real ML-DSA parameter set follows. -/
theorem trivial_euf_cma_security_of_nma_short (maxAttempts : ℕ) :
    ∃ (mlweReduction : LearningWithErrors.Adversary (mldsaMatrixMLWE p))
      (stmsisReduction : SelfTargetMSIS.Adversary (mldsaSTMSISShort p prims M)),
      (trivialForger p prims M maxAttempts).advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal
          (LearningWithErrors.advantage (mldsaMatrixMLWE p) mlweReduction + 1) +
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss 0 0 1 0 1 1 zero_lt_one) :=
  euf_cma_security_of_nma_short p prims (mldsaMatrixMLWE p) (mldsaSTMSISShort p prims M)
    maxAttempts (hrShort p prims) rfl rfl (neverAbortSim p prims) 1 zero_le_one
    (neverAbortSim_hvzk p prims) 0 0 1 0 1 zero_le_one zero_le_one le_rfl zero_lt_one
    (honestNoAbortGood p prims)
    (by rw [ENNReal.ofReal_one]; exact probEvent_le_one)
    (fun _pk _sk _h _cm => by rw [ENNReal.ofReal_one]; exact probOutput_le_one)
    (fun _pk _sk h => by rw [ENNReal.ofReal_zero]; exact h.le)
    (fun pk _sk _h => by
      rw [ENNReal.ofReal_zero]; exact (probOutput_none_neverAbortSim p prims pk).le)
    (trivialForger p prims M maxAttempts)
    (trivialForger_signHashQueryBound p prims M maxAttempts)
    1
    (fun main =>
      ⟨matrixLift p prims (distinguisherBShort p prims (hrShort p prims) maxAttempts main),
        advantage_mldsaMLWEShort_le_matrix p prims (expandAIdealization_one p prims) _⟩)

end ShortCMAWitness

end MLDSA
