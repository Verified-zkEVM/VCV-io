/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.HypertreeGeneral

/-!
# Query bounds for the general SLH-DSA hypertree

These bounds count calls in the free public-hash program.  They are uniform in the message and
depend on `d` exactly through the FIPS Algorithm 12/13 layer schedule.
-/

@[expose] public section

namespace SLHDSA.GeneralHypertree

open OracleComp

variable {p : Params}

/-- One XMSS signature without the discarded root recovery. -/
def xmssSignQueryBound (p : Params) : ℕ :=
  p.len * (p.w - 1) + xmssAuthPathQueryBound p p.hp

/-- Recovery of one intrinsically sized XMSS signature. -/
def xmssRecoverQueryBound (p : Params) : ℕ :=
  p.len * (p.w - 1) + 1 + p.hp

/-- One XMSS signature followed by recovery of its root. -/
def xmssCycleQueryBound (p : Params) : ℕ :=
  p.len * (p.w - 1) + 1 + xmssAuthPathQueryBound p p.hp + p.hp

/-- Recursive Algorithm 12 budget.  Only the `d = 1` entry call recovers its final component. -/
def signLoopQueryBound (p : Params) (recoverFinal : Bool) : ℕ → ℕ
  | 0 => 0
  | 1 => if recoverFinal then xmssCycleQueryBound p else xmssSignQueryBound p
  | layers + 2 => xmssCycleQueryBound p + signLoopQueryBound p false (layers + 1)

/-- Closed Algorithm 12 budget, including the FIPS-mandated discarded recovery for `d = 1`. -/
def signQueryBound (p : Params) : ℕ :=
  if p.d = 1 then xmssCycleQueryBound p
  else (p.d - 1) * xmssCycleQueryBound p + xmssSignQueryBound p

/-- Algorithm 13 recovers exactly one XMSS signature at every layer. -/
def recoverQueryBound (p : Params) : ℕ :=
  p.d * xmssRecoverQueryBound p

private theorem chainSteps_sum_le (core : CorePrimitives p) (msg : core.Y) :
    (∑ i : Fin p.len, chainStepsCore core msg i.val) ≤ p.len * (p.w - 1) := by
  calc
    (∑ i : Fin p.len, chainStepsCore core msg i.val) ≤
        ∑ _ : Fin p.len, (p.w - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact chainStepsCore_le core msg i.val
    _ = p.len * (p.w - 1) := by simp

private theorem complementaryChainSteps_sum_le (core : CorePrimitives p) (msg : core.Y) :
    (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) ≤
      p.len * (p.w - 1) := by
  calc
    (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) ≤
        ∑ _ : Fin p.len, (p.w - 1) := by
      apply Finset.sum_le_sum
      intro i _
      omega
    _ = p.len * (p.w - 1) := by simp

private theorem chainSteps_partition (core : CorePrimitives p) (msg : core.Y) :
    (∑ i : Fin p.len, chainStepsCore core msg i.val) +
        (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) =
      p.len * (p.w - 1) := by
  rw [← Finset.sum_add_distrib]
  simp_rw [Nat.add_sub_of_le (chainStepsCore_le core msg _)]
  simp

theorem xmssSignM_isTotalQueryBound_coarse (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound
      (xmssSignM core msg sk pk adrs idx :
        OracleComp (publicHashSpec core) (XmssSig p core))
      (xmssSignQueryBound p) := by
  apply (xmssSignM_isTotalQueryBound core msg sk pk adrs idx).mono
  unfold xmssSignQueryBound
  have := chainSteps_sum_le core msg
  omega

theorem xmssPkFromSigM_isTotalQueryBound_coarse (core : CorePrimitives p)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssPkFromSigM core idx sig msg pk adrs :
        OracleComp (publicHashSpec core) core.Y)
      (xmssRecoverQueryBound p) := by
  apply (xmssPkFromSigM_isTotalQueryBound core idx sig msg pk adrs).mono
  unfold xmssRecoverQueryBound
  have := complementaryChainSteps_sum_le core msg
  omega

/-- Signing and recovery while retaining both results has the same complete-chain budget as the
existing root-only composition theorem. -/
theorem xmssSignRecoverPairM_isTotalQueryBound (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM core msg sk pk adrs idx
      let root ← xmssPkFromSigM core idx sig msg pk adrs
      return (sig, root)) :
        OracleComp (publicHashSpec core) (XmssSig p core × core.Y))
      (xmssCycleQueryBound p) := by
  have hbound := isTotalQueryBound_bind
    (xmssSignM_isTotalQueryBound core msg sk pk adrs idx) fun sig =>
      isTotalQueryBound_bind
        (xmssPkFromSigM_isTotalQueryBound core idx sig msg pk adrs) fun root =>
          show IsTotalQueryBound
            (pure (sig, root) : OracleComp (publicHashSpec core) _) 0 from trivial
  unfold xmssCycleQueryBound
  have hpartition := chainSteps_partition core msg
  simpa [← Nat.add_assoc, hpartition, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound

theorem signFromPositionM_isTotalQueryBound (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (sk : core.SkSeed) (pk : core.PkSeed)
    (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    IsTotalQueryBound
      (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg :
        OracleComp (publicHashSpec core) (Vector (XmssSig vp.params core) layers))
      (signLoopQueryBound vp.params recoverFinal layers) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => trivial
  | one =>
      cases recoverFinal with
      | false =>
          simpa [signFromPositionM, signFromPositionWith, xmssSignM,
            signLoopQueryBound] using
            isTotalQueryBound_bind
              (xmssSignM_isTotalQueryBound_coarse core msg sk pk pos.toAdrs pos.leaf.val)
              (fun sig => show IsTotalQueryBound
                (pure #v[sig] : OracleComp (publicHashSpec core) _) 0 from trivial)
      | true =>
          have hbound := isTotalQueryBound_bind
            (xmssSignRecoverPairM_isTotalQueryBound core msg sk pk pos.toAdrs pos.leaf.val)
            (fun sigAndRoot => show IsTotalQueryBound
              (pure #v[sigAndRoot.1] : OracleComp (publicHashSpec core) _) 0 from trivial)
          simpa [signFromPositionM, signFromPositionWith, xmssSignM, xmssPkFromSigM,
            signLoopQueryBound, bind_assoc] using hbound
  | more layers _ ih =>
      let next := pos.next (by omega)
      have hbound := isTotalQueryBound_bind
        (xmssSignRecoverPairM_isTotalQueryBound core msg sk pk pos.toAdrs pos.leaf.val)
        (fun pair => isTotalQueryBound_bind
          (ih (recoverFinal := false) (pos := next)
            (hremaining := by simp [next]; omega) (msg := pair.2))
          (fun rest => show IsTotalQueryBound
            (pure (rest.insertIdx 0 pair.1) : OracleComp (publicHashSpec core) _) 0 from trivial))
      simpa [signFromPositionM, signFromPositionWith, xmssSignM, xmssPkFromSigM,
        signLoopQueryBound, next, bind_assoc] using hbound

theorem recoverFromPositionM_isTotalQueryBound (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (pk : core.PkSeed) (pos : LayerPosition vp)
    (layers : ℕ) (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    IsTotalQueryBound
      (recoverFromPositionM vp core pk pos layers hremaining msg sigs :
        OracleComp (publicHashSpec core) core.Y)
      (layers * xmssRecoverQueryBound vp.params) := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => trivial
  | one =>
      simpa [recoverFromPositionM, recoverFromPositionWith, xmssPkFromSigM] using
        xmssPkFromSigM_isTotalQueryBound_coarse core pos.leaf.val sigs.head msg pk pos.toAdrs
  | more layers _ ih =>
      let next := pos.next (by omega)
      have hbound := isTotalQueryBound_bind
        (xmssPkFromSigM_isTotalQueryBound_coarse core pos.leaf.val sigs.head msg pk pos.toAdrs)
        (fun root => ih (pos := next) (hremaining := by simp [next]; omega)
          (msg := root) (sigs := sigs.tail))
      simpa [recoverFromPositionM, recoverFromPositionWith, xmssPkFromSigM, next,
        Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using hbound

theorem signLoopQueryBound_false (p : Params) (layers : ℕ) (hlayers : 0 < layers) :
    signLoopQueryBound p false layers =
      (layers - 1) * xmssCycleQueryBound p + xmssSignQueryBound p := by
  induction layers using Nat.twoStepInduction with
  | zero => omega
  | one => simp [signLoopQueryBound]
  | more layers _ ih =>
      have ih' := ih (by omega)
      rw [show layers + 1 - 1 = layers by omega] at ih'
      rw [signLoopQueryBound, ih', show layers + 2 - 1 = layers + 1 by omega,
        Nat.succ_mul]
      ac_rfl

theorem signM_isTotalQueryBound (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    IsTotalQueryBound
      (signM vp core msg sk pk parts :
        OracleComp (publicHashSpec core) (Signature vp core))
      (signQueryBound vp.params) := by
  have h := signFromPositionM_isTotalQueryBound vp core sk pk
    (vp.params.d == 1) (LayerPosition.initial vp parts) vp.params.d
    (by simp) msg
  by_cases hd : vp.params.d = 1
  · have htrue : (vp.params.d == 1) = true := by simp [hd]
    simpa only [signM, signQueryBound, hd, htrue, beq_self_eq_true, signLoopQueryBound,
      if_true] using h
  · have hfalse : (vp.params.d == 1) = false := by simp [hd]
    rw [hfalse, signLoopQueryBound_false vp.params vp.params.d vp.valid.d_pos] at h
    simpa [signM, signQueryBound, hd, hfalse] using h

theorem pkFromSigM_isTotalQueryBound (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (msg : core.Y) (sig : Signature vp core)
    (pk : core.PkSeed) (parts : DigestParts vp.params) :
    IsTotalQueryBound
      (pkFromSigM vp core msg sig pk parts : OracleComp (publicHashSpec core) core.Y)
      (recoverQueryBound vp.params) := by
  simpa [pkFromSigM, recoverQueryBound] using
    recoverFromPositionM_isTotalQueryBound vp core pk (LayerPosition.initial vp parts)
      vp.params.d (by simp) msg sig

end SLHDSA.GeneralHypertree
