/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.Fischlin.Completeness

/-!
# Fischlin online extraction and logged verification
-/

public section

universe u v

open OracleComp OracleSpec

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

open ENNReal OracleComp.EvalDist

section security

variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (ρ b S : ℕ) (M : Type) [DecidableEq M]

/-! ### Online Extraction / Knowledge Soundness -/

/-- Structural query bound: the computation makes at most `Q` total hash oracle queries
(`Sum.inr` queries), with no restriction on `unifSpec` queries (`Sum.inl`).

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the right (random-oracle) component of the index sum. -/
@[expose]
def ROQueryBound {α : Type}
    (oa : OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M) α)
    (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inr _) Q

/-- A cheating prover (knowledge soundness adversary) for the Fischlin transform.
The adversary receives a statement and message, has access to both the random oracle
and internal randomness (`unifSpec`), and attempts to produce a valid Fischlin proof
without knowing the witness.

The Σ-protocol `σ` is not referenced in the structure itself (only in the
extraction and verification steps of the experiment), so it enters the
theorem statements via hypotheses like `σ.SpeciallySound`. -/
structure KnowledgeSoundnessAdv where
  run : Stmt → M → OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
    (FischlinProof Commit Chal Resp ρ)

/-- Online extractor for the Fischlin transform (Fischlin 2005, Construction 2).

Given statement `x`, a proof `π`, and the log of all hash oracle queries made by
the prover, the extractor searches for two accepting transcripts at the same
commitment with different challenges, then invokes the Σ-protocol's `extract`
function. Returns `none` if no such collision is found in the log.

The key property enabling this extractor is `UniqueResponses`: given the same
`(statement, commitment, challenge)`, there is at most one valid response.
So finding a second valid query at a different challenge gives a proper
input pair for the Σ-protocol extractor. -/
@[expose]
def onlineExtract
    (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) : ProbComp (Option Wit) :=
  let comList := List.ofFn fun i => (π i).1
  let findWitness : Fin ρ → Option (Chal × Resp × Chal × Resp) := fun i =>
    let (com_i, ω_i, _resp_i) := π i
    log.findSome? fun ⟨entry, _⟩ =>
      if entry.stmt == x && entry.comList == comList && entry.rep == i
          && σ.verify x com_i entry.chal entry.resp
          && decide (entry.chal ≠ ω_i) then
        some (ω_i, (π i).2.2, entry.chal, entry.resp)
      else none
  match (List.finRange ρ).findSome? findWitness with
  | some (ω₁, p₁, ω₂, p₂) => some <$> σ.extract ω₁ p₁ ω₂ p₂
  | none => return none

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- The deterministic log scan performed by `onlineExtract`: search the repetitions for a logged
random-oracle query at the proof's statement/commitment-list/repetition tags that verifies
against the proof's commitment with a challenge different from the proof's challenge.
Definitionally equal to the internal `findSome?` of `onlineExtract` (see
`onlineExtract_eq_match`). -/
private def fischlinFindWitness (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    Option (Chal × Resp × Chal × Resp) :=
  let comList := List.ofFn fun i => (π i).1
  (List.finRange ρ).findSome? fun i =>
    let (com_i, ω_i, _resp_i) := π i
    log.findSome? fun ⟨entry, _⟩ =>
      if entry.stmt == x && entry.comList == comList && entry.rep == i
          && σ.verify x com_i entry.chal entry.resp
          && decide (entry.chal ≠ ω_i) then
        some (ω_i, (π i).2.2, entry.chal, entry.resp)
      else none

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- `onlineExtract` is exactly a match on `fischlinFindWitness`. -/
private lemma onlineExtract_eq_match (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    onlineExtract σ ρ b M x π log =
      match fischlinFindWitness σ ρ b M x π log with
      | some (ω₁, p₁, ω₂, p₂) => some <$> σ.extract ω₁ p₁ ω₂ p₂
      | none => return none := rfl

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- If the scan fires, every element of the support of `onlineExtract` is `some` of a valid
witness (given special soundness and per-repetition verification of the final proof). -/
private lemma onlineExtract_support_of_findWitness_ne_none
    (hss : σ.SpeciallySound)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true)
    (hfw : fischlinFindWitness σ ρ b M x π log ≠ none) :
    ∀ e ∈ support (onlineExtract σ ρ b M x π log),
      ∃ w : Wit, e = some w ∧ rel x w = true := by
  intro e he
  obtain ⟨⟨ω₁, p₁, ω₂, p₂⟩, hfw'⟩ := Option.ne_none_iff_exists'.mp hfw
  have he' : e ∈ support (some <$> σ.extract ω₁ p₁ ω₂ p₂) := by
    rw [onlineExtract_eq_match, hfw'] at he
    exact he
  rw [support_map] at he'
  obtain ⟨w, hw, rfl⟩ := he'
  refine ⟨w, rfl, ?_⟩
  -- Unpack the scan hit: a repetition `i` and a log entry passing the filter.
  obtain ⟨i, hi, hfi⟩ := List.exists_of_findSome?_eq_some hfw'
  obtain ⟨⟨entry, hv⟩, he2, hfe⟩ := List.exists_of_findSome?_eq_some hfi
  dsimp only at hfe
  split at hfe
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨hstmt, hcom⟩, hrep⟩, hverE⟩, hneq⟩ := hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hfe
    obtain ⟨h1, h2, h3, h4⟩ := hfe
    subst h1; subst h2; subst h3; subst h4
    exact σ.extract_sound_of_speciallySoundAt (hss x) (Ne.symm hneq) (hver i) hverE hw
  · exact absurd hfe (by simp)

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- Every `some w` in the support of `onlineExtract` is a valid witness, given special soundness
and per-repetition verification of the final proof. -/
private lemma onlineExtract_some_valid
    (hss : σ.SpeciallySound)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true) :
    ∀ w : Wit, some w ∈ support (onlineExtract σ ρ b M x π log) → rel x w = true := by
  intro w hw
  by_cases hfw : fischlinFindWitness σ ρ b M x π log = none
  · -- The scan missed: the extractor returns `none`, so `some w` is not in the support.
    rw [onlineExtract_eq_match, hfw] at hw
    simp at hw
  · obtain ⟨w', hw', hrel⟩ :=
      onlineExtract_support_of_findWitness_ne_none σ ρ b M hss hver hfw _ hw
    cases Option.some.inj hw'
    exact hrel

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- If the extractor's scan finds nothing, then every log entry matching a repetition's
`(stmt, comList, rep)` tags and verifying against the proof's commitment carries exactly the
proof's challenge. -/
private lemma chal_pinned_of_findWitness_none
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hnone : fischlinFindWitness σ ρ b M x π log = none)
    (i : Fin ρ)
    (e : (_t : FischlinROInput Stmt Commit Chal Resp ρ M) × Fin (2 ^ b))
    (he : e ∈ log)
    (hstmt : e.1.stmt = x) (hcom : e.1.comList = List.ofFn fun j => (π j).1)
    (hrep : e.1.rep = i) (hverE : σ.verify x (π i).1 e.1.chal e.1.resp = true) :
    e.1.chal = (π i).2.1 := by
  by_contra hne
  rw [fischlinFindWitness, List.findSome?_eq_none_iff] at hnone
  have hi : log.findSome? (fun e' =>
      if e'.1.stmt == x && e'.1.comList == (List.ofFn fun j => (π j).1) && e'.1.rep == i
          && σ.verify x (π i).1 e'.1.chal e'.1.resp
          && decide (e'.1.chal ≠ (π i).2.1) then
        some ((π i).2.1, (π i).2.2, e'.1.chal, e'.1.resp)
      else none) = none := hnone i (List.mem_finRange i)
  rw [List.findSome?_eq_none_iff] at hi
  have hfe := hi e he
  rw [if_pos (by simp [hstmt, hcom, hrep, hverE, hne])] at hfe
  exact Option.some_ne_none _ hfe

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- Under `UniqueResponses`, if additionally the final proof verifies at repetition `i`, a
matching log entry carries exactly the proof's challenge *and response*. -/
private lemma resp_pinned_of_findWitness_none
    (hur : σ.UniqueResponses)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hnone : fischlinFindWitness σ ρ b M x π log = none)
    (i : Fin ρ)
    (hveri : σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true)
    (e : (_t : FischlinROInput Stmt Commit Chal Resp ρ M) × Fin (2 ^ b))
    (he : e ∈ log)
    (hstmt : e.1.stmt = x) (hcom : e.1.comList = List.ofFn fun j => (π j).1)
    (hrep : e.1.rep = i) (hverE : σ.verify x (π i).1 e.1.chal e.1.resp = true) :
    e.1.chal = (π i).2.1 ∧ e.1.resp = (π i).2.2 := by
  have hchal : e.1.chal = (π i).2.1 :=
    chal_pinned_of_findWitness_none σ ρ b M hnone i e he hstmt hcom hrep hverE
  exact ⟨hchal, hur x (π i).1 (π i).2.1 e.1.resp (π i).2.2 (hchal ▸ hverE) hveri⟩

/-- Soundness error bound for the Fischlin transform (Fischlin 2005, Theorem 2).

For `Q` total hash oracle queries, `ρ` repetitions, `b`-bit hashes, and max sum `S`:
the error is `(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

For `S = 0` this simplifies to `(Q + 1) / 2^(bρ)`.
The intended regime is `0 < ρ`; theorem statements below make that explicit. -/
@[expose] noncomputable def knowledgeSoundnessError (Q ρ b S : ℕ) : ℝ≥0∞ :=
  (↑(Q + 1) : ℝ≥0∞) * ↑((S + 1) * Nat.choose (S + ρ - 1) (ρ - 1)) /
    ((↑(2 ^ b) : ℝ≥0∞) ^ ρ)

/-- The knowledge soundness experiment for the Fischlin transform.

Runs a cheating prover with a logged random oracle, then checks:
1. Whether the Fischlin verifier accepts the produced proof.
2. Whether the online extractor returns a witness satisfying the relation.

Returns `true` (the "bad event") when verification succeeds but the extracted
output is either `none` or an invalid witness.

The `prover` argument is the raw function rather than `KnowledgeSoundnessAdv`
to keep type inference tractable. -/
@[expose]
def knowledgeSoundnessExp
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) : ProbComp Bool :=
  let roSpec := fischlinROSpec Stmt Commit Chal Resp ρ b M
  let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
  let loggedRO := ro.withLogging
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (WriterT (QueryLog roSpec) (StateT roSpec.QueryCache ProbComp))
  do
    let ((π, roLog), cache) ← (simulateQ (idImpl + loggedRO) (prover x msg)).run |>.run ∅
    let idImpl' := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT roSpec.QueryCache ProbComp)
    let (verified, _) ←
      (simulateQ (idImpl' + ro)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify x msg π)).run cache
    let extracted ← onlineExtract σ ρ b M x π roLog
    return (verified && !(match extracted with | some w => rel x w | none => false))

/-- The verification step of `knowledgeSoundnessExp`, as a standalone computation
(definitionally the same term). -/
private def ksVerify (x : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :
    ProbComp (Bool × (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) :=
  let roSpec := fischlinROSpec Stmt Commit Chal Resp ρ b M
  let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
  let idImpl' := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT roSpec.QueryCache ProbComp)
  (simulateQ (idImpl' + ro)
    ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
      σ hr ρ b S M).verify x msg π)).run cache

/-- The sampling phase of `knowledgeSoundnessExp` (prover run + verification), keeping the proof,
the random-oracle log, and the verdict, but discarding the extractor. -/
private def ksSample
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    ProbComp ((FischlinProof Commit Chal Resp ρ ×
      QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) × Bool) :=
  let roSpec := fischlinROSpec Stmt Commit Chal Resp ρ b M
  let ro : QueryImpl roSpec (StateT roSpec.QueryCache ProbComp) := randomOracle
  let loggedRO := ro.withLogging
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (WriterT (QueryLog roSpec) (StateT roSpec.QueryCache ProbComp))
  do
    let ((π, roLog), cache) ← (simulateQ (idImpl + loggedRO) (prover x msg)).run |>.run ∅
    let idImpl' := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT roSpec.QueryCache ProbComp)
    let (verified, _) ←
      (simulateQ (idImpl' + ro)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify x msg π)).run cache
    return ((π, roLog), verified)

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- If the scan fires (and the proof verifies per repetition), the "bad-output" map of the
extractor result never produces `true`. -/
private lemma probOutput_onlineExtract_bad_eq_zero
    (hss : σ.SpeciallySound)
    {x : Stmt} {π : FischlinProof Commit Chal Resp ρ}
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    (hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true)
    (hfw : fischlinFindWitness σ ρ b M x π log ≠ none) :
    Pr[= true | do
      let e ← onlineExtract σ ρ b M x π log
      return !(match e with | some w => rel x w | none => false)] = 0 := by
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun e => ?_
  by_cases he : e ∈ support (onlineExtract σ ρ b M x π log)
  · obtain ⟨w, rfl, hrel⟩ :=
      onlineExtract_support_of_findWitness_ne_none σ ρ b M hss hver hfw e he
    simp [hrel]
  · simp [probOutput_eq_zero_of_not_mem_support he]

omit [SampleableType Chal] in
/-- **Bad-event bridge.** The bad event of the knowledge-soundness experiment is bounded by the
probability that the verifier accepts while the extractor's scan misses.

The hypothesis `hverSupp` isolates the remaining combinatorial fact about the Fischlin verifier:
any accepting run of the (simulated) verifier implies per-repetition Σ-verification of the proof
(the Σ-verification bits inside `Fischlin.verify` are deterministic, independent of the oracle
answers). -/
private lemma knowledgeSoundnessExp_bad_le_misses
    (hss : σ.SpeciallySound)
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M)
    (hverSupp : ∀ (π : FischlinProof Commit Chal Resp ρ)
      (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
      (c' : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache),
      (true, c') ∈ support (ksVerify σ hr ρ b S M x msg π cache) →
      ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M prover x msg] ≤
      Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg] := by
  simp only [knowledgeSoundnessExp, ksSample]
  rw [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl ?_
  obtain ⟨⟨π', roLog'⟩, cache'⟩ := a
  rw [probOutput_bind_eq_tsum_subtype, probEvent_bind_eq_tsum_subtype]
  refine ENNReal.tsum_le_tsum fun vc => mul_le_mul' le_rfl ?_
  obtain ⟨⟨v, c'⟩, hvc⟩ := vc
  cases v with
  | false =>
    have hzero : Pr[= true | do
        let _e ← onlineExtract σ ρ b M x π' roLog'
        return false] = 0 := by
      simp
    exact le_trans (le_of_eq hzero) zero_le
  | true =>
    by_cases hfw : fischlinFindWitness σ ρ b M x π' roLog' = none
    · refine le_trans probOutput_le_one (le_of_eq ?_)
      rw [probEvent_pure]
      simp [hfw]
    · have hver := hverSupp π' cache' c' hvc
      have hzero := probOutput_onlineExtract_bad_eq_zero σ ρ b M hss hver hfw
      exact le_trans (le_of_eq hzero) zero_le

/-- The lifted `unifSpec` forwarder on the logging stack, exactly as in
`knowledgeSoundnessExp`. -/
private def idImplW {ι : Type} (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp))

/-- The logged random oracle, exactly as in `knowledgeSoundnessExp`. -/
private def loggedROW {ι : Type} (hashSpec : OracleSpec ι) [DecidableEq ι]
     [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] :
    QueryImpl hashSpec (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  (hashSpec.randomOracle).withLogging

/-- The combined logging implementation, exactly the `idImpl + loggedRO` of
`knowledgeSoundnessExp` and `ksSample`. -/
private def compositeW {ι : Type} (hashSpec : OracleSpec ι) [DecidableEq ι]
     [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] :
    QueryImpl (unifSpec + hashSpec)
      (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  idImplW hashSpec + loggedROW hashSpec

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The lifted unifSpec forwarder neither logs nor touches the cache. -/
private lemma idImplW_run_run {ι : Type} (hashSpec : OracleSpec ι)
    (i : unifSpec.Domain) (c : hashSpec.QueryCache) :
    ((idImplW hashSpec i).run).run c =
      (fun u => ((u, (∅ : QueryLog hashSpec)), c)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) i) := by
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Cache hit: the logged random oracle returns the cached value, logs it, leaves the cache. -/
private lemma loggedROW_run_run_some {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
     [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {t : hashSpec.Domain} {c : hashSpec.QueryCache} {u : hashSpec.Range t}
    (h : c t = some u) :
    ((loggedROW hashSpec t).run).run c = pure ((u, ([⟨t, u⟩] : QueryLog hashSpec)), c) := by
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_some _ h, pure_bind]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Cache miss: the logged random oracle samples, caches the value, and logs it. -/
private lemma loggedROW_run_run_none {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
     [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {t : hashSpec.Domain} {c : hashSpec.QueryCache} (h : c t = none) :
    ((loggedROW hashSpec t).run).run c =
      (fun u => ((u, ([⟨t, u⟩] : QueryLog hashSpec)), c.cacheQuery t u)) <$>
        ($ᵗ hashSpec.Range t) := by
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_none _ h]
  rw [show uniformSampleImpl (spec := hashSpec) t = ($ᵗ hashSpec.Range t) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Master log↔cache correspondence.** For any run of the Fischlin-style logging composite
from cache `cache₀` (and an empty ambient log), every support outcome `((a, log), cache')`
satisfies: the cache only grows, every logged entry is in the final cache with the same value,
and every final cache entry was either logged or already present in `cache₀`. -/
private theorem mem_support_run_correspondence {ι : Type} {hashSpec : OracleSpec ι}
    [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] {α : Type}
    (oa : OracleComp (unifSpec + hashSpec) α)
    (cache₀ : hashSpec.QueryCache)
    (z : (α × QueryLog hashSpec) × hashSpec.QueryCache)
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run cache₀)) :
    cache₀ ≤ z.2 ∧
      (∀ e ∈ z.1.2, z.2 e.1 = some e.2) ∧
      (∀ (t : hashSpec.Domain) (u : hashSpec.Range t), z.2 t = some u →
        (⟨t, u⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 ∨ cache₀ t = some u) := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨le_rfl, fun e he => ?_, fun t u hu => Or.inr hu⟩
      simp only [List.empty_eq, List.not_mem_nil] at he
  | query_bind t k ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨⟨⟨u, w₁⟩, c₁⟩, hp, hrest⟩ := hz
      rw [StateT.run_map, support_map] at hrest
      obtain ⟨⟨⟨a₂, w₂⟩, c₂⟩, hmem₂, hzeq⟩ := hrest
      subst hzeq
      obtain ⟨hmono, hT1, hT2⟩ := ih _ c₁ _ hmem₂
      cases t with
      | inl i =>
          change ((u, w₁), c₁) ∈ support (((idImplW hashSpec i).run).run cache₀) at hp
          rw [idImplW_run_run, support_map] at hp
          obtain ⟨v, hv, hpe⟩ := hp
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpe
          refine ⟨hmono, ?_, ?_⟩
          · intro e he
            simp only [Prod.map, id, List.empty_eq, List.nil_append] at he ⊢
            exact hT1 e he
          · intro t' u' hu'
            simp only [Prod.map, id, List.empty_eq, List.nil_append]
            exact hT2 t' u' hu'
      | inr j =>
          change ((u, w₁), c₁) ∈ support (((loggedROW hashSpec j).run).run cache₀) at hp
          cases hc : cache₀ j with
          | some u₀ =>
              rw [loggedROW_run_run_some hc, support_pure] at hp
              have hp' : ((u, w₁), c₁) = ((u₀, [⟨j, u₀⟩]), cache₀) := hp
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp'
              refine ⟨hmono, ?_, ?_⟩
              · intro e he
                simp only [Prod.map, id, List.cons_append, List.nil_append,
                  List.mem_cons] at he ⊢
                rcases he with rfl | he
                · exact hmono hc
                · exact hT1 e he
              · intro t' u' hu'
                simp only [Prod.map, id, List.cons_append, List.nil_append, List.mem_cons]
                rcases hT2 t' u' hu' with h | h
                · exact Or.inl (Or.inr h)
                · exact Or.inr h
          | none =>
              rw [loggedROW_run_run_none hc, support_map] at hp
              obtain ⟨v, hv, hpe⟩ := hp
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpe
              change hashSpec.Range j at u
              refine ⟨le_trans (QueryCache.le_cacheQuery _ hc) hmono, ?_, ?_⟩
              · intro e he
                simp only [Prod.map, id, List.cons_append, List.nil_append,
                  List.mem_cons] at he ⊢
                rcases he with rfl | he
                · exact hmono (QueryCache.cacheQuery_self cache₀ j u)
                · exact hT1 e he
              · intro t' u' hu'
                simp only [Prod.map, id, List.cons_append, List.nil_append, List.mem_cons]
                rcases hT2 t' u' hu' with h | h
                · exact Or.inl (Or.inr h)
                · by_cases ht : t' = j
                  · subst ht
                    rw [QueryCache.cacheQuery_self] at h
                    exact Or.inl (Or.inl (by rw [Option.some.injEq] at h; rw [h]))
                  · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h
                    exact Or.inr h

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Every logged entry is in the final cache with the same value (run from `∅`). -/
private theorem log_subset_cache {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ e ∈ z.1.2, z.2 e.1 = some e.2 :=
  (mem_support_run_correspondence oa ∅ z hz).2.1

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Every final cache entry was logged (run from `∅`). -/
private theorem cache_subset_log {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ (t : hashSpec.Domain) (u : hashSpec.Range t), z.2 t = some u →
      (⟨t, u⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 := fun t u hu =>
  ((mem_support_run_correspondence oa ∅ z hz).2.2 t u hu).resolve_right (by simp)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each domain point has a unique logged value (run from `∅`). -/
private theorem log_unique {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ (t : hashSpec.Domain) (u₁ u₂ : hashSpec.Range t),
      (⟨t, u₁⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 →
      (⟨t, u₂⟩ : (s : hashSpec.Domain) × hashSpec.Range s) ∈ z.1.2 → u₁ = u₂ := by
  intro t u₁ u₂ h₁ h₂
  have e₁ := log_subset_cache oa hz ⟨t, u₁⟩ h₁
  have e₂ := log_subset_cache oa hz ⟨t, u₂⟩ h₂
  exact Option.some.inj (e₁.symm.trans e₂)

/-- The cache-side pinning predicate: every cached record carrying the proof's
statement/commitment-list tags whose challenge–response pair verifies (at its own repetition
index) carries exactly the proof's challenge at that repetition. The `msg` field of the record
is not inspected, mirroring the extractor's log scan. -/
private def CachePinned (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : Prop :=
  ∀ (r : FischlinROInput Stmt Commit Chal Resp ρ M) (u : Fin (2 ^ b)),
    cache r = some u → r.stmt = x → r.comList = (List.ofFn fun j => (π j).1) →
    σ.verify x (π r.rep).1 r.chal r.resp = true → r.chal = (π r.rep).2.1

omit [DecidableEq Resp] [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]
  [DecidableEq M] in
/-- **Log↔cache transfer.** Under the log↔cache correspondence, the extractor's scan misses
iff the cache-side pinning predicate holds. -/
private theorem fischlinFindWitness_eq_none_iff_cachePinned
    (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    {log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)}
    {cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache}
    (hT1 : ∀ e ∈ log, cache e.1 = some e.2)
    (hT2 : ∀ (t : FischlinROInput Stmt Commit Chal Resp ρ M) (u : Fin (2 ^ b)),
      cache t = some u →
        (⟨t, u⟩ : (_s : FischlinROInput Stmt Commit Chal Resp ρ M) × Fin (2 ^ b)) ∈ log) :
    fischlinFindWitness σ ρ b M x π log = none ↔ CachePinned σ ρ b M x π cache := by
  constructor
  · -- scan-none → cache predicate, via cached ⇒ logged ⇒ pinning.
    intro hnone r u hru hstmt hcom hver
    exact chal_pinned_of_findWitness_none σ ρ b M hnone r.rep ⟨r, u⟩ (hT2 r u hru)
      hstmt hcom rfl hver
  · -- cache predicate → scan-none, via logged ⇒ cached ⇒ predicate applies.
    intro hpin
    rw [fischlinFindWitness, List.findSome?_eq_none_iff]
    intro i _hi
    rw [List.findSome?_eq_none_iff]
    intro e he
    dsimp only
    split
    · rename_i hcond
      exfalso
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨⟨hstmt, hcom⟩, hrep⟩, hver⟩, hne⟩ := hcond
      apply hne
      have hpinned := hpin e.1 e.2 (hT1 e he) hstmt hcom (by rw [hrep]; exact hver)
      rw [hpinned, hrep]
    · rfl

end security

end Fischlin
