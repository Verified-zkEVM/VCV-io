/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.Fork
import VCVio.CryptoFoundations.ReplayFork

/-!
# Fiat-Shamir forking infrastructure

Wraps a managed-RO NMA adversary against `FiatShamir` into a single-oracle
`OracleComp (unifSpec + (Unit →ₒ Chal))` computation that `ReplayFork` can
fork. Collects the forgery, the adversary's cache, the live query log, and a
`verified` flag, and exposes a `forkPoint` that picks the index at which to
rewind.

The main export is `Fork.replayForkingBound`: the Fiat-Shamir-specific
analogue of Firsov-Janku's `forking_lemma_ro`, stated at the `OracleComp`
level. Callers in `FiatShamir.Sigma.Security` compose it with
`ReplayFork.forkReplay_propertyTransfer` to drive the NMA-to-extraction step
of `euf_nma_bound`.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

namespace Fork

/-- Trace used by the Fiat-Shamir forking reduction for managed-RO NMA adversaries. -/
structure Trace where
  forgery : M × (Commit × Resp)
  advCache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache
  roCache : (M × Commit →ₒ Chal).QueryCache
  queryLog : List (M × Commit)
  verified : Bool

/-- The hash point corresponding to the final forgery recorded in a fork trace. -/
def Trace.target
    (trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    M × Commit :=
  (trace.forgery.1, trace.forgery.2.1)

/-- Rewinding point extracted from a managed-RO fork trace. The fork is usable exactly when
the final forgery verifies and its hash point appears in the live query log. -/
def forkPoint
    [DecidableEq M] [DecidableEq Commit]
    (qH : ℕ)
    (trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    Option (Fin (qH + 1)) := by
  if hverified : trace.verified then
    let target := trace.target
    if hmem : target ∈ trace.queryLog then
      let idx := trace.queryLog.findIdx (· == target)
      if hidx : idx < qH + 1 then
        exact some ⟨idx, hidx⟩
      else
        exact none
    else
      exact none
  else
    exact none

lemma forkPoint_some_imp_verified
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.verified = true := by
  unfold forkPoint at hs
  by_cases hverified : trace.verified
  · exact hverified
  · simp [hverified] at hs

lemma forkPoint_some_imp_mem
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.target ∈ trace.queryLog := by
  unfold forkPoint at hs
  by_cases hverified : trace.verified
  · have hs' :
        trace.target ∈ trace.queryLog ∧
          ∃ h : trace.queryLog.findIdx (· == trace.target) ≤ qH,
            (⟨trace.queryLog.findIdx (· == trace.target), Nat.lt_succ_of_le h⟩ :
              Fin (qH + 1)) = s := by
        simpa [hverified, Trace.target] using hs
    exact hs'.1
  · simp [hverified] at hs

lemma forkPoint_getElem?_eq_some_target
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.queryLog[↑s]? = some trace.target := by
  unfold forkPoint at hs
  by_cases hverified : trace.verified
  · have hs' :
        trace.target ∈ trace.queryLog ∧
          ∃ h : trace.queryLog.findIdx (· == trace.target) ≤ qH,
            (⟨trace.queryLog.findIdx (· == trace.target), Nat.lt_succ_of_le h⟩ :
              Fin (qH + 1)) = s := by
        simpa [hverified, Trace.target] using hs
    rcases hs' with ⟨hmem, ⟨hidx, hs'⟩⟩
    have hlt : trace.queryLog.findIdx (· == trace.target) < trace.queryLog.length := by
      exact List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩
    subst s
    exact (List.getElem_eq_iff
      (l := trace.queryLog)
      (i := trace.queryLog.findIdx (· == trace.target))
      (x := trace.target)
      hlt).mp <|
      by
        simpa [Trace.target] using
          (List.findIdx_getElem (xs := trace.queryLog) (p := fun x => x == trace.target)
            (w := hlt))
  · simp [hverified] at hs

/-- Replay a managed-RO NMA adversary against a single counted challenge oracle, keeping both
the adversary-returned cache and the live query log that the forking lemma can rewind.

The `verified` flag is computed only from challenge values already present in one of those
two caches. In particular, this trace does not perform a fresh post-hoc verification query;
it records exactly the executions whose forgery is already determined by the adversary's
managed view of the random oracle. -/
noncomputable def runTrace
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (unifSpec + (Unit →ₒ Chal))
      (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := by
  let origSpec := unifSpec + (M × Commit →ₒ Chal)
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  let wrappedSpec := unifSpec + chalSpec
  let simSt := (M × Commit →ₒ Chal).QueryCache × List (M × Commit)
  let unifFwd : QueryImpl unifSpec
      (StateT simSt (OracleComp wrappedSpec)) :=
    fun n => monadLift
      (liftM (query (spec := wrappedSpec) (Sum.inl n)) :
        OracleComp wrappedSpec _)
  let roImpl : QueryImpl (M × Commit →ₒ Chal)
      (StateT simSt (OracleComp wrappedSpec)) :=
    fun mc => do
      let (cache, log) ← get
      match cache mc with
      | some v => pure v
      | none =>
          let v : Chal ← monadLift
            (liftM (query (spec := wrappedSpec) (Sum.inr ())) :
              OracleComp wrappedSpec Chal)
          set ((cache.cacheQuery mc v : (M × Commit →ₒ Chal).QueryCache),
            log ++ [mc])
          pure v
  exact do
    let ((forgery, advCache), st) ←
      StateT.run (simulateQ (unifFwd + roImpl) (nmaAdv.main pk)) (∅, [])
    let verified :=
      match forgery with
      | (msg, (c, s)) =>
          match advCache (Sum.inr (msg, c)) with
          | some ω => σ.verify pk c ω s
          | none =>
              match st.1 (msg, c) with
              | some ω => σ.verify pk c ω s
              | none => false
    let (roCache, queryLog) := st
    pure {
      forgery := forgery
      advCache := advCache
      roCache := roCache
      queryLog := queryLog
      verified := verified
    }

/-- Forkable managed-RO NMA experiment. Success means the final forged transcript verifies and
the corresponding hash point appears in the live query log, so the forking lemma can rewind it. -/
noncomputable def exp
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ProbComp Bool :=
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := chalSpec))) (do
      let (pk, _) ←
        OracleComp.liftComp hr.gen (unifSpec + chalSpec)
      let trace ← runTrace σ hr M nmaAdv pk
      pure (forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
        qH trace).isSome)

/-- The forkable success probability of a managed-RO NMA adversary. -/
noncomputable def advantage
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ENNReal :=
  Pr[= true | exp σ hr M nmaAdv qH]

/-- Managed-RO replay-fork convenience theorem at a fixed public key, stated at the
`OracleComp (unifSpec + (Unit →ₒ Chal))` level.

This is the Fiat-Shamir-specific analogue of Firsov-Janku's `forking_lemma_ro` at
[fsec/proof/ForkingRO.ec:443](../../../fsec/proof/ForkingRO.ec). It packages the replay
quantitative bound with the distinct-answer and postcondition-transfer facts for the wrapped
managed random-oracle trace experiment, composing `le_probEvent_isSome_forkReplay`
(quantitative bound) and `forkReplay_propertyTransfer` (postcondition transfer).

**On the level of the statement.** We state the bound at the `OracleComp` level rather than
lifting through `simulateQ` to `ProbComp`. Each caller (e.g. `euf_nma_bound`) can bridge to
`ProbComp` in one line using `uniformSampleImpl.probEvent_simulateQ` when needed, keeping this
lemma focused on the forking-lemma content.

**On the target-equality conjunct.** A maximally-informative version would also conclude
`x₁.target = x₂.target` (i.e. message-commit pair coincidence at the fork point), matching
Firsov-Janku's `forking_lemma_ro`. In the Lean formalization this conjunct is consumed by the
downstream reduction `euf_nma_bound` to align the cached challenges `ω_i = x_i.roCache target`.
Since it relies on a value-level log-prefix invariant across `replayRunWithTraceValue` plus a
correspondence between the adversary's internal `queryLog` and the outer `QueryLog`, it is
extracted through the caller-provided `P_out` transfer predicate: the caller may choose `P_out`
so that `P_out x log` pins `x.target` to a deterministic function of `(log, cf x)`, and then
derive target-equality from the distinct-answer disagreement on the outer log. -/
theorem replayForkingBound
    [DecidableEq M] [DecidableEq Commit]
    [DecidableEq Chal] [SampleableType Chal] [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    (P_out : Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      QueryLog (unifSpec + (Unit →ₒ Chal)) → Prop)
    (hP : ∀ {x log},
      (x, log) ∈ support (replayFirstRun (runTrace σ hr M nmaAdv pk)) →
      P_out x log) :
    let wrappedMain := runTrace σ hr M nmaAdv pk
    let cf := forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
    let qb : ℕ ⊕ Unit → ℕ := fun j => match j with | .inl _ => 0 | .inr () => qH
    let acc := Pr[ fun x => (cf x).isSome | wrappedMain]
    acc * (acc / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr[
        fun r : Option
            (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
          ∃ (x₁ x₂ :
              Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
            (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
            r = some (x₁, x₂) ∧
            cf x₁ = some s ∧
            cf x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
              QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
            P_out x₁ log₁ ∧
            P_out x₂ log₂
        | forkReplay wrappedMain qb (Sum.inr ()) cf] := by
  intro wrappedMain cf qb acc
  -- Step 1: Rewrite `acc` as `∑ s, Pr[= some s | cf <$> wrappedMain]`, matching the LHS of
  -- `le_probEvent_isSome_forkReplay`.
  classical
  have hAcc_sum :
      acc = ∑ s, Pr[= some s | cf <$> wrappedMain] := by
    simp only [acc]
    rw [show (fun x => (cf x).isSome = true) =
        (fun x : _ => (Option.isSome x = true)) ∘ cf from rfl,
      ← probEvent_map (q := fun r => Option.isSome r = true)]
    rw [probEvent_eq_tsum_ite]
    rw [tsum_option _ ENNReal.summable]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
      ↓reduceIte, zero_add]
    rw [tsum_fintype]
  rw [hAcc_sum]
  -- Step 2: Apply the forking lemma lower bound `le_probEvent_isSome_forkReplay`,
  -- then upgrade the RHS event from `isSome` to the structural postcondition using
  -- `forkReplay_propertyTransfer` through `probEvent_mono`.
  have hH_inv : (Fintype.card ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr ())) : ENNReal)⁻¹ =
      challengeSpaceInv Chal := rfl
  have hqb_eq : qb (Sum.inr ()) = qH := rfl
  calc (∑ s, Pr[= some s | cf <$> wrappedMain]) *
        ((∑ s, Pr[= some s | cf <$> wrappedMain]) / (↑qH + 1) - challengeSpaceInv Chal)
      = (∑ s, Pr[= some s | cf <$> wrappedMain]) *
        ((∑ s, Pr[= some s | cf <$> wrappedMain]) / ↑(qb (Sum.inr ()) + 1)
          - challengeSpaceInv Chal) := by rw [hqb_eq]; push_cast; ring_nf
    _ ≤ Pr[ fun r : Option
            (Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
              r.isSome | forkReplay wrappedMain qb (Sum.inr ()) cf] := by
        have hbound := le_probEvent_isSome_forkReplay
          (main := wrappedMain) (qb := qb) (i := Sum.inr ()) (cf := cf)
        simp only at hbound
        rw [hH_inv] at hbound
        exact hbound
    _ ≤ _ := by
        apply probEvent_mono
        intro r hr hisSome
        rcases r with _ | ⟨x₁, x₂⟩
        · simp at hisSome
        obtain ⟨log₁, log₂, s, hcf₁, hcf₂, hP₁, hP₂, hneq⟩ :=
          forkReplay_propertyTransfer
            (main := wrappedMain) (qb := qb) (i := Sum.inr ()) (cf := cf)
            (P_out := P_out) (hP := hP) hr
        exact ⟨x₁, x₂, s, log₁, log₂, rfl, hcf₁, hcf₂, hneq, hP₁, hP₂⟩

end Fork

end FiatShamir
