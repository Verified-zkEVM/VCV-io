/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Data.Nat.Choose.Cast
public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Bodies
public import VCVio.CryptoFoundations.FiatShamir.QueryBounds
public import VCVio.ProgramLogic.Relational.SimulateQ
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# EUF-CMA for Fiat-Shamir with aborts: Loss

The CMA-to-NMA statistical loss of the Fiat-Shamir-with-aborts reduction
(after Theorem 3, CRYPTO 2023): `cmaToNmaLoss` and its per-key part `perKeyLoss`.

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

/-- The classical ROM statistical loss of the Fiat-Shamir-with-aborts CMA-to-NMA
reduction (after Theorem 3, CRYPTO 2023), for a per-attempt HVZK simulator:

`L = 2·qS·(qH+1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk/(1-p) + δ`

where:
- `qS` / `qH`: signing-oracle / adversarial random-oracle query bounds;
- `ε`: per-key commitment-guessing probability bound (on good keys);
- `p`: per-key, per-attempt abort probability bound (on good keys), for both the honest
  prover and the simulator;
- `ζ_zk`: total-variation error of the HVZK simulator for one signing **attempt**, over
  optional transcripts (`none` = abort), as in `IdenSchemeWithAbort.HVZK`;
- `δ`: probability that key generation falls outside the good-key event.

The first term pays for reprogramming collisions with adversarial hash queries (both in
the all-attempts-reprogram hybrid and in the accepted-only-reprogram hybrid, hence the
factor 2; the `qH + 1` accounts for the final verification query). The second term pays
for collisions among the signing oracle's own commitments. The third term glues the
per-attempt simulator across the restart loop, whose expected length is at most
`1/(1-p)` (see `tvDist_firstSome_le_geometric`); a simulator for the accepted-transcript
distribution itself (the paper's acHVZK notion) would shave this `1/(1-p)` factor. -/
@[expose] noncomputable def cmaToNmaLoss (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (_hp : p < 1) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk / (1 - p) +
  δ

/-- The per-key part of `cmaToNmaLoss`: the statistical loss of the three signing-oracle
hybrid hops at a fixed good key pair. `cmaToNmaLoss` is this quantity plus the
key-regularity failure probability `δ`. -/
@[expose] noncomputable def perKeyLoss (qS qH : ℕ) (ε p ζ_zk : ℝ) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk / (1 - p)

lemma cmaToNmaLoss_eq_perKeyLoss_add (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (hp : p < 1) :
    cmaToNmaLoss qS qH ε p ζ_zk δ hp = perKeyLoss qS qH ε p ζ_zk + δ := rfl

end EUF_CMA

end FiatShamirWithAbort
