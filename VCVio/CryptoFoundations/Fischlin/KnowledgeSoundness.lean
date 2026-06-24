/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import VCVio.CryptoFoundations.Fischlin.Completeness

/-!
# Fischlin Transform: Online Extraction / Knowledge Soundness

Online (straight-line) knowledge soundness for the Fischlin transform: the
extractor `onlineExtract` observes the prover's random-oracle queries, and the
extraction failure probability is bounded via a supermartingale potential
argument, culminating in `knowledgeSoundness`.
-/

universe u v

open OracleComp OracleSpec

namespace Fischlin

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

open ENNReal

section security

variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal]

variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
  (hr : GenerableRelation Stmt Wit rel)
  (ρ b S : ℕ) (M : Type) [DecidableEq M]

/-! ### Online Extraction / Knowledge Soundness -/

/-- Structural query bound: the computation makes at most `Q` total hash oracle queries
(`Sum.inr` queries), with no restriction on `unifSpec` queries (`Sum.inl`).

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the right (random-oracle) component of the index sum. -/
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
noncomputable def onlineExtract
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
noncomputable def knowledgeSoundnessError (Q ρ b S : ℕ) : ℝ≥0∞ :=
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
noncomputable def knowledgeSoundnessExp
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
private noncomputable def ksVerify (x : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ)
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
private noncomputable def ksSample
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
    exact le_trans (le_of_eq hzero) zero_le'
  | true =>
    by_cases hfw : fischlinFindWitness σ ρ b M x π' roLog' = none
    · refine le_trans probOutput_le_one (le_of_eq ?_)
      rw [probEvent_pure]
      simp [hfw]
    · have hver := hverSupp π' cache' c' hvc
      have hzero := probOutput_onlineExtract_bad_eq_zero σ ρ b M hss hver hfw
      exact le_trans (le_of_eq hzero) zero_le'

/-- The lifted `unifSpec` forwarder on the logging stack, exactly as in
`knowledgeSoundnessExp`. -/
private noncomputable def idImplW {ι : Type} (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp))

/-- The logged random oracle, exactly as in `knowledgeSoundnessExp`. -/
private noncomputable def loggedROW {ι : Type} (hashSpec : OracleSpec ι) [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] :
    QueryImpl hashSpec (WriterT (QueryLog hashSpec) (StateT hashSpec.QueryCache ProbComp)) :=
  (hashSpec.randomOracle).withLogging

/-- The combined logging implementation, exactly the `idImpl + loggedRO` of
`knowledgeSoundnessExp` and `ksSample`. -/
private noncomputable def compositeW {ι : Type} (hashSpec : OracleSpec ι) [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)] :
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
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
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
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
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
    [DecidableEq ι] [hashSpec.DecidableEq]
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
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    {z : (α × QueryLog hashSpec) × hashSpec.QueryCache}
    (hz : z ∈ support (((simulateQ (compositeW hashSpec) oa).run).run ∅)) :
    ∀ e ∈ z.1.2, z.2 e.1 = some e.2 :=
  (mem_support_run_correspondence oa ∅ z hz).2.1

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Every final cache entry was logged (run from `∅`). -/
private theorem cache_subset_log {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
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
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
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

/-- The number of hash-value tuples `v : Fin ρ → Fin (2^b)` whose entries sum to at most `S`.

This counts the "small-sum" verifier-accepting hash assignments: a Fischlin proof is accepted only
when `∑ᵢ H(…,ωᵢ,respᵢ) ≤ S`, so this finite set is the target the prover's fresh random-oracle
answers must hit. It is bounded by `(S+1)·C(S+ρ-1, ρ-1)` (stars-and-bars). -/
def smallSumCount (ρ b S : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)).card

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Stars-and-bars bound.** The number of hash-value tuples summing to at most `S` is at most
`(S+1)·C(S+ρ-1, ρ-1)`.

Each `Fin (2^b)`-valued tuple injects into a `Fin ρ → ℕ` tuple with the same (bounded) sum; the
number of such natural tuples with sum exactly `s` is `C(s+ρ-1, ρ-1)`, which is monotone in `s`, so
summing over the `S+1` values `s = 0, …, S` gives the stated bound. -/
private lemma smallSumCount_le :
    smallSumCount ρ b S ≤ (S + 1) * Nat.choose (S + ρ - 1) (ρ - 1) := by
  classical
  -- Per-fiber count: tuples `Fin ρ → ℕ` summing to exactly `s` number `C(ρ+s-1, s)`.
  have hfiber : ∀ s : ℕ, (Finset.univ.piAntidiag s : Finset (Fin ρ → ℕ)).card
      = (ρ + s - 1).choose s := by
    intro s
    rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
      Sym.card_sym_eq_choose, Fintype.card_fin]
  -- The `Fin.val` image of a small-sum hash tuple lands in the union of exact-sum natural tuples.
  set T : Finset (Fin ρ → ℕ) :=
    (Finset.range (S + 1)).biUnion (fun s => Finset.univ.piAntidiag s) with hT
  have hmap : (Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)).image
      (fun v i => (v i).val) ⊆ T := by
    intro g hg
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    simp only [hT, Finset.mem_biUnion, Finset.mem_range, Finset.mem_piAntidiag,
      Finset.mem_univ, implies_true, and_true]
    exact ⟨∑ i, (v i).val, by omega, rfl⟩
  -- The image has the same cardinality (the map `v ↦ Fin.val ∘ v` is injective).
  have hinj : Set.InjOn (fun v : Fin ρ → Fin (2 ^ b) => fun i => (v i).val)
      ↑(Finset.univ.filter (fun v : Fin ρ → Fin (2 ^ b) => ∑ i, (v i).val ≤ S)) := by
    intro v₁ _ v₂ _ h
    funext i
    exact Fin.val_injective (congrFun h i)
  rw [smallSumCount, ← Finset.card_image_of_injOn hinj]
  refine le_trans (Finset.card_le_card hmap) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [Finset.sum_congr rfl (fun s _ => hfiber s)]
  -- Each fiber count is at most `C(S+ρ-1, ρ-1)`; there are `S+1` of them.
  refine le_trans (Finset.sum_le_card_nsmul _ _ ((S + ρ - 1).choose (ρ - 1)) (fun s hs => ?_)) ?_
  · rw [Finset.mem_range] at hs
    rcases Nat.eq_zero_or_pos ρ with hρ0 | hρpos
    · subst hρ0
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : 0 + s - 1 < s)]; exact Nat.zero_le _
    · have h1 : (ρ + s - 1).choose s = (ρ + s - 1).choose (ρ - 1) := by
        rw [← Nat.choose_symm (by omega)]; congr 1; omega
      rw [h1]; exact Nat.choose_le_choose _ (by omega)
  · rw [Finset.card_range, smul_eq_mul]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each output tuple of `n` IID uniform draws is equally likely, with probability
`(Fintype.card α)⁻¹ ^ n`. -/
private lemma probOutput_mOfFn_uniformSample {α : Type} [SampleableType α] [Fintype α]
    (n : ℕ) (w : Fin n → α) :
    Pr[= w | Fin.mOfFn n (fun _ => ($ᵗ α : ProbComp α))]
      = (Fintype.card α : ℝ≥0∞)⁻¹ ^ n := by
  letI : DecidableEq α := Classical.decEq α
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := funext fun i => i.elim0
    simp [Fin.mOfFn, hw]
  | succ n ih =>
    have hcond : ∀ (a : α) (r : Fin n → α),
        w = Fin.cons a r ↔ r = Fin.tail w ∧ a = w 0 := by
      intro a r
      constructor
      · rintro rfl
        simp
      · rintro ⟨rfl, rfl⟩
        exact (Fin.cons_self_tail w).symm
    rw [Fin.mOfFn]
    simp only [probOutput_bind_eq_tsum, probOutput_pure, ih, probOutput_uniformSample,
      hcond, ite_and, mul_ite, mul_one, mul_zero, tsum_ite_eq]
    rw [pow_succ']

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The probability that `n` IID uniform draws land in a (decidable) target set is exactly the
size of the target set over `(Fintype.card α) ^ n`. -/
private lemma probEvent_mOfFn_uniformSample {α : Type} [SampleableType α] [Fintype α]
    (n : ℕ) (p : (Fin n → α) → Prop) [DecidablePred p] :
    Pr[p | Fin.mOfFn n (fun _ => ($ᵗ α : ProbComp α))]
      = ((Finset.univ.filter p).card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ n := by
  rw [probEvent_eq_sum_filter_univ]
  simp only [probOutput_mOfFn_uniformSample, Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv, ENNReal.inv_pow]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Untouched slot completes with probability exactly `μ`.** The probability that `ρ` fresh
uniform `Fin (2^b)` draws sum to at most `S` is exactly `smallSumCount ρ b S / (2^b)^ρ`. -/
private lemma probEvent_sum_le_mOfFn_uniform :
    Pr[fun v => ∑ i, (v i).val ≤ S | Fin.mOfFn ρ (fun _ => $ᵗ (Fin (2 ^ b)))]
      = (smallSumCount ρ b S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ ρ := by
  rw [probEvent_mOfFn_uniformSample, Fintype.card_fin, smallSumCount]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Conditional tail.** Given a revealed partial sum `T ≤ S`, the probability that `k` fresh
uniform draws bring the total to at most `S` is exactly `smallSumCount k b (S - T) / (2^b)^k`.
This is the per-slot completion probability with some coordinates already revealed, used by the
potential-function step of the knowledge-soundness bound. -/
private lemma probEvent_add_sum_le_mOfFn_uniform (k T : ℕ) (hT : T ≤ S) :
    Pr[fun v => T + ∑ i, (v i).val ≤ S | Fin.mOfFn k (fun _ => $ᵗ (Fin (2 ^ b)))]
      = (smallSumCount k b (S - T) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ k := by
  have hfilter :
      (Finset.univ.filter (fun v : Fin k → Fin (2 ^ b) => T + ∑ i, (v i).val ≤ S))
        = (Finset.univ.filter (fun v : Fin k → Fin (2 ^ b) => ∑ i, (v i).val ≤ S - T)) :=
    Finset.filter_congr fun v _ => by omega
  rw [probEvent_mOfFn_uniformSample k
      (fun v : Fin k → Fin (2 ^ b) => T + ∑ i, (v i).val ≤ S),
    Fintype.card_fin, smallSumCount, hfilter]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Mixed-cache query vector.** Simulating a `Fin.mOfFn` of random-oracle re-queries at
pairwise distinct records on a cache that stores exactly the `hits`-marked records: each hit
reads its cached value deterministically; each miss draws a fresh uniform `Fin (2^b)` (and
caches it, which never collides with the remaining records by injectivity). The output
distribution is the independent per-index product `pure (hit value) / $ᵗ Fin (2^b)`. The
all-hit special case is `run_mOfFn_query_hit`. -/
private lemma run'_mOfFn_query_mixed {β : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hinj : Function.Injective records)
    (hits : Fin n → Option (Fin (2 ^ b)))
    (f : Fin n → Fin (2 ^ b) → β)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hcache : ∀ i, cache (records i) = hits i) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        (Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h))).run' cache]
      = 𝒟[(fun u => fun i => f i (u i)) <$>
          Fin.mOfFn n fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] := by
  induction n generalizing cache with
  | zero =>
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run'_pure', map_pure]
      exact congrArg (fun z => 𝒟[(pure z : ProbComp (Fin 0 → β))]) (funext fun i => i.elim0)
  | succ n ih =>
      -- Tail step, shared by both branches: with head answer `x` and any cache `c` storing
      -- `hits ∘ Fin.succ` at the tail records, the tail simulation matches the model tail.
      have hstep : ∀ (x : Fin (2 ^ b))
          (c : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache),
          (∀ j : Fin n, c (records j.succ) = hits j.succ) →
          𝒟[(simulateQ (fischlinImpl ρ b M)
              (Fin.mOfFn n (fun j => do
                let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M)
                  (records j.succ)
                pure (f j.succ h)) >>= fun rest => pure (Fin.cons (f 0 x) rest))).run' c]
            = 𝒟[(fun u : Fin n → Fin (2 ^ b) => fun i : Fin (n + 1) =>
                  f i ((Fin.cons x u : Fin (n + 1) → Fin (2 ^ b)) i)) <$>
                Fin.mOfFn n fun j =>
                  match hits j.succ with
                  | some h => (pure h : ProbComp (Fin (2 ^ b)))
                  | none => $ᵗ Fin (2 ^ b)] := by
        intro x c hc
        rw [bind_pure_comp, simulateQ_map, StateT.run'_map']
        refine (evalDist_map_eq_of_evalDist_eq
          (ih (fun j => records j.succ)
            (fun j₁ j₂ hj => Fin.succ_injective n (hinj hj))
            (fun j => hits j.succ) (fun j => f j.succ) c hc)
          (Fin.cons (α := fun _ => β) (f 0 x))).trans ?_
        rw [Functor.map_map]
        refine congrArg evalDist (congrArg (· <$> _) ?_)
        funext u i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [Fin.cons_zero]
        · simp [Fin.cons_succ]
      -- Freshness of tail records is preserved by caching the head record (distinct records).
      have hcache' : ∀ (x : Fin (2 ^ b)) (j : Fin n),
          (cache.cacheQuery (records 0) x) (records j.succ) = hits j.succ := by
        intro x j
        have hne : records j.succ ≠ records 0 := fun hEq => Fin.succ_ne_zero j (hinj hEq)
        exact (QueryCache.cacheQuery_of_ne cache x hne).trans (hcache j.succ)
      cases hh : hits 0 with
      | some h0 =>
          have hc0 : cache (records 0) = some h0 := by rw [hcache 0, hh]
          simp only [Fin.mOfFn]
          rw [simulateQ_bind, StateT.run'_bind', simulateQ_bind,
            roSim.simulateQ_HasQuery_query, StateT.run_bind,
            QueryImpl.withCaching_run_some (so := uniformSampleImpl) hc0]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure]
          rw [hstep h0 cache (fun j => hcache j.succ)]
          simp only [hh, pure_bind, bind_pure_comp, Functor.map_map]
      | none =>
          have hc0 : cache (records 0) = none := by rw [hcache 0, hh]
          simp only [Fin.mOfFn]
          rw [simulateQ_bind, StateT.run'_bind', simulateQ_bind,
            roSim.simulateQ_HasQuery_query, StateT.run_bind,
            QueryImpl.withCaching_run_none (so := uniformSampleImpl) hc0]
          simp only [uniformSampleImpl, bind_map_left, pure_bind, simulateQ_pure,
            StateT.run_pure, bind_assoc]
          simp only [hh, map_bind]
          rw [evalDist_bind, evalDist_bind]
          refine congrArg (𝒟[$ᵗ Fin (2 ^ b)] >>= ·) (funext fun x => ?_)
          rw [hstep x (cache.cacheQuery (records 0) x) (hcache' x)]
          simp only [map_pure, bind_pure_comp]

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- Same as `run'_mOfFn_query_mixed`, packaged with a pure verdict post-processing `V` of the
per-repetition results, matching the shape of `Fischlin`'s verifier. -/
private lemma run'_mOfFn_query_mixed_bind {β γ : Type} (n : ℕ)
    (records : Fin n → (fischlinROSpec Stmt Commit Chal Resp ρ b M).Domain)
    (hinj : Function.Injective records)
    (hits : Fin n → Option (Fin (2 ^ b)))
    (f : Fin n → Fin (2 ^ b) → β) (V : (Fin n → β) → γ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hcache : ∀ i, cache (records i) = hits i) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        ((Fin.mOfFn n fun i => do
          let h ← HasQuery.query (spec := fischlinROSpec Stmt Commit Chal Resp ρ b M) (records i)
          pure (f i h)) >>= fun results => pure (V results))).run' cache]
      = 𝒟[(Fin.mOfFn n fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)) >>= fun u => pure (V fun i => f i (u i))] := by
  rw [bind_pure_comp V, simulateQ_map, StateT.run'_map']
  refine (evalDist_map_eq_of_evalDist_eq
    (run'_mOfFn_query_mixed ρ b M n records hinj hits f cache hcache) V).trans ?_
  rw [Functor.map_map, bind_pure_comp]

omit [SampleableType Chal] in
/-- **Mixed-cache verify run.** The Fischlin verifier's `run'` on a cache storing exactly the
`hits`-marked records: re-queries at hit records read the cached hash; misses sample fresh
uniforms. The `ρ` records are pairwise distinct (their `rep` field is the repetition index),
so within one verify run each record is queried exactly once. -/
private lemma verify_run'_mixed (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hits : Fin ρ → Option (Fin (2 ^ b)))
    (hcache : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = hits i) :
    𝒟[(simulateQ (fischlinImpl ρ b M)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify pk msg sig)).run' cache]
      = 𝒟[(Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)) >>= fun u =>
          pure (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
            decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S))] := by
  refine (run'_mOfFn_query_mixed_bind ρ b M ρ
    (records := fun i =>
      ⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩)
    (hinj := fun i j h => congrArg FischlinROInput.rep h)
    (hits := hits)
    (f := fun i h => (σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2, h.val))
    (V := fun results => ((List.finRange ρ).all fun i => (results i).1) &&
      decide ((List.finRange ρ).foldl (fun acc i => acc + (results i).2) 0 ≤ S))
    cache hcache).trans ?_
  rfl

/-- The number of hash-value tuples extending the cached `hits` with total sum at most `S`.

Counts full tuples `v : Fin ρ → Fin (2^b)` that agree with every cached hit and have small sum;
each such tuple corresponds to exactly one assignment of the miss positions. For
`hits = fun _ => none` this is `smallSumCount ρ b S` (see `partialSmallSumCount_none`). -/
private def partialSmallSumCount (ρ b : ℕ) (hits : Fin ρ → Option (Fin (2 ^ b))) (S : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin ρ → Fin (2 ^ b) =>
    (∀ i h, hits i = some h → v i = h) ∧ ∑ i, (v i).val ≤ S).card

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- With no cached hits, the partial small-sum count is the full small-sum count. -/
private lemma partialSmallSumCount_none :
    partialSmallSumCount ρ b (fun _ => none) S = smallSumCount ρ b S := by
  unfold partialSmallSumCount smallSumCount
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  simp

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Output probabilities of an independent product `Fin.mOfFn` multiply coordinatewise. -/
private lemma probOutput_mOfFn {α : Type} [Finite α] (n : ℕ)
    (g : Fin n → ProbComp α) (v : Fin n → α) :
    Pr[= v | Fin.mOfFn n g] = ∏ i, Pr[= v i | g i] := by
  letI : Fintype α := Fintype.ofFinite α
  letI : DecidableEq α := Classical.decEq α
  induction n with
  | zero =>
      have hv : v = Fin.elim0 := funext fun i => i.elim0
      subst hv
      simp [Fin.mOfFn, probOutput_pure]
  | succ n ih =>
      simp only [Fin.mOfFn]
      rw [probOutput_bind_eq_sum_fintype]
      have hinner : ∀ a : α,
          Pr[= v | Fin.mOfFn n (fun i => g i.succ) >>= fun rest => pure (Fin.cons a rest)]
            = if a = v 0 then Pr[= Fin.tail v | Fin.mOfFn n fun i => g i.succ] else 0 := by
        intro a
        rw [probOutput_bind_eq_sum_fintype]
        have hiff : ∀ rest : Fin n → α,
            (v = Fin.cons a rest) ↔ (a = v 0 ∧ rest = Fin.tail v) := by
          intro rest
          constructor
          · intro hEq
            refine ⟨by rw [hEq, Fin.cons_zero], funext fun k => ?_⟩
            have := congrFun hEq k.succ
            rw [Fin.cons_succ] at this
            exact this.symm
          · rintro ⟨rfl, rfl⟩
            exact (Fin.cons_self_tail v).symm
        by_cases ha : a = v 0
        · rw [if_pos ha]
          subst ha
          simp only [probOutput_pure, hiff, true_and]
          simp [mul_ite]
        · rw [if_neg ha]
          refine Finset.sum_eq_zero fun rest _ => ?_
          rw [probOutput_pure, if_neg (fun hEq => ha ((hiff rest).mp hEq).1), mul_zero]
      simp only [hinner, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (v 0)
        (fun a => Pr[= a | g 0] * Pr[= Fin.tail v | Fin.mOfFn n fun i => g i.succ]),
        if_pos (Finset.mem_univ _), ih, Fin.prod_univ_succ]
      rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Sum the per-repetition fold into a `Finset.sum`. -/
private lemma foldl_add_eq_sum (u : Fin ρ → Fin (2 ^ b)) :
    (List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 = ∑ i, (u i).val := by
  have hgen : ∀ (l : List (Fin ρ)) (init : ℕ),
      l.foldl (fun acc i => acc + (u i).val) init = init + (l.map fun i => (u i).val).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a l ihl => intro init; simp [ihl, Nat.add_assoc]
  rw [hgen, Nat.zero_add, ← List.ofFn_eq_map, List.sum_ofFn]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The product of per-coordinate hit/miss probabilities: zero unless `u` extends the hits,
in which case it is `(2^b)⁻¹` per miss. -/
private lemma prob_extend_hits (hits : Fin ρ → Option (Fin (2 ^ b))) (u : Fin ρ → Fin (2 ^ b)) :
    Pr[= u | Fin.mOfFn ρ fun i =>
        match hits i with
        | some h => (pure h : ProbComp (Fin (2 ^ b)))
        | none => $ᵗ Fin (2 ^ b)]
      = if ∀ i h, hits i = some h → u i = h
          then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ ^ (Finset.univ.filter fun i : Fin ρ => hits i = none).card
          else 0 := by
  rw [probOutput_mOfFn]
  by_cases hcomp : ∀ i h, hits i = some h → u i = h
  · rw [if_pos hcomp]
    have hfactor : ∀ i : Fin ρ,
        Pr[= u i | (match hits i with
          | some h => (pure h : ProbComp (Fin (2 ^ b)))
          | none => $ᵗ Fin (2 ^ b))]
          = if hits i = none then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ else 1 := by
      intro i
      cases hh : hits i with
      | none =>
          simp only [if_true]
          rw [probOutput_uniformSample, Fintype.card_fin]
      | some h =>
          have hu : u i = h := hcomp i h hh
          rw [probOutput_pure, if_pos hu, if_neg (Option.some_ne_none h)]
    rw [Finset.prod_congr rfl fun i _ => hfactor i, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  · rw [if_neg hcomp]
    push Not at hcomp
    obtain ⟨i, h, hh, hne⟩ := hcomp
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [hh]
    rw [probOutput_pure, if_neg hne]

omit [SampleableType Chal] in
/-- **The ψ leaf (exact).** The probability that the Fischlin verifier accepts on a cache
storing exactly the `hits`-marked records is EXACTLY the σ-verification indicator times the
number of hit-compatible small-sum hash tuples over the miss-space volume `(2^b)^#misses`.

For `hits = fun _ => none` (the all-fresh case) the bound specializes to
`smallSumCount ρ b S / (2^b)^ρ` via `partialSmallSumCount_none`. -/
private lemma verify_probOutput_true_mixed (pk : Stmt) (msg : M)
    (sig : Fin ρ → Commit × Chal × Resp)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (hits : Fin ρ → Option (Fin (2 ^ b)))
    (hcache : ∀ i, cache (⟨pk, msg, List.ofFn (fun j => (sig j).1), i, (sig i).2.1, (sig i).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M) = hits i) :
    Pr[= true | (simulateQ (fischlinImpl ρ b M)
        ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
          σ hr ρ b S M).verify pk msg sig)).run' cache]
      = (if ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = true
          then 1 else 0) *
        (partialSmallSumCount ρ b hits S : ℝ≥0∞) /
          (((2 ^ b : ℕ) : ℝ≥0∞)) ^ (Finset.univ.filter fun i : Fin ρ => hits i = none).card := by
  rw [probOutput_def, verify_run'_mixed σ hr ρ b S M pk msg sig cache hits hcache,
    ← probOutput_def, probOutput_bind_eq_sum_fintype]
  by_cases haV :
      ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = true
  · -- σ-verification accepted: the verdict is exactly the small-sum event.
    have hterm : ∀ u : Fin ρ → Fin (2 ^ b),
        Pr[= u | Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] *
          Pr[= true | (pure
            (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
              decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S)) :
            ProbComp Bool)]
          = if (∀ i h, hits i = some h → u i = h) ∧ ∑ i, (u i).val ≤ S
              then (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹ ^
                (Finset.univ.filter fun i : Fin ρ => hits i = none).card
              else 0 := by
      intro u
      rw [prob_extend_hits ρ b hits u, probOutput_pure, foldl_add_eq_sum ρ b u, haV]
      by_cases h3 : ∀ i h, hits i = some h → u i = h <;>
        by_cases h2 : (∑ i, (u i).val) ≤ S <;>
        simp [h3, h2]
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, if_pos haV, one_mul, div_eq_mul_inv, ← ENNReal.inv_pow]
    rfl
  · -- σ-verification rejected: the verdict is constantly `false`.
    have haV' :
        ((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) = false :=
      Bool.eq_false_iff.mpr haV
    have hterm0 : ∀ u : Fin ρ → Fin (2 ^ b),
        Pr[= u | Fin.mOfFn ρ fun i =>
            match hits i with
            | some h => (pure h : ProbComp (Fin (2 ^ b)))
            | none => $ᵗ Fin (2 ^ b)] *
          Pr[= true | (pure
            (((List.finRange ρ).all fun i => σ.verify pk (sig i).1 (sig i).2.1 (sig i).2.2) &&
              decide ((List.finRange ρ).foldl (fun acc i => acc + (u i).val) 0 ≤ S)) :
            ProbComp Bool)]
          = 0 := by
      intro u
      rw [haV', probOutput_pure]
      simp
    rw [Finset.sum_congr rfl fun u _ => hterm0 u, Finset.sum_const_zero, if_neg haV, zero_mul,
      ENNReal.zero_div]

omit [SampleableType Chal] in
/-- **Accepting verify runs Σ-verify every repetition.** Any `(true, _)` outcome in the support
of the simulated Fischlin verifier implies the per-repetition Σ-protocol checks of the proof:
the Σ-verification bits inside `verify` are deterministic and independent of the oracle
answers, so a `false` bit forces acceptance probability zero. Discharges the `hverSupp`
hypothesis of `knowledgeSoundnessExp_bad_le_misses`. -/
private lemma ksVerify_true_support_allVerified (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (c' : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (h : (true, c') ∈ support (ksVerify σ hr ρ b S M x msg π cache)) :
    ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true := by
  intro i
  by_contra hne
  have hall : ((List.finRange ρ).all fun j => σ.verify x (π j).1 (π j).2.1 (π j).2.2) ≠ true :=
    fun hAll => hne (List.all_eq_true.mp hAll i (List.mem_finRange i))
  have hmem : true ∈ support ((simulateQ (fischlinImpl ρ b M)
      ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify x msg π)).run' cache) := by
    rw [StateT.run', support_map]
    exact ⟨(true, c'), h, rfl⟩
  have hpos := probOutput_pos _ _ hmem
  rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache
    (fun j => cache (⟨x, msg, List.ofFn (fun k => (π k).1), j, (π j).2.1, (π j).2.2⟩ :
      FischlinROInput Stmt Commit Chal Resp ρ M)) (fun j => rfl),
    if_neg hall, zero_mul, ENNReal.zero_div] at hpos
  exact lt_irrefl 0 hpos

omit [SampleableType Chal] in
/-- `knowledgeSoundnessExp_bad_le_misses` with the verifier-determinism hypothesis discharged:
the knowledge-soundness bad event is bounded by the probability that the verifier accepts
while the extractor's scan misses. -/
private lemma knowledgeSoundnessExp_bad_le_misses' (hss : σ.SpeciallySound)
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M prover x msg] ≤
      Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg] :=
  knowledgeSoundnessExp_bad_le_misses σ hr ρ b S M hss prover x msg
    (fun π cache c' h => ksVerify_true_support_allVerified σ hr ρ b S M x msg π cache c' h)

/-- Number of unrevealed coordinates of a partial hash assignment. -/
private def missCard {ρ b : ℕ} (g : Fin ρ → Option (Fin (2 ^ b))) : ℕ :=
  (Finset.univ.filter fun i => g i = none).card

/-- Per-slot potential: the current conditional completion probability of a slot given the
revealed coordinates `g`. An untouched slot has potential exactly
`μ = smallSumCount ρ b S / (2^b)^ρ` (`slotPsi_none`), and revealing one fresh uniform
coordinate is a martingale step (`slotPsi_tower`). -/
private noncomputable def slotPsi (ρ b S : ℕ) (g : Fin ρ → Option (Fin (2 ^ b))) : ℝ≥0∞ :=
  (partialSmallSumCount ρ b g S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ (missCard g)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Fiberwise decomposition: summing the extension counts over the possible values of a fresh
coordinate recovers the count for the unextended assignment (tower property at the level of
counting). -/
private lemma sum_partialSmallSumCount_update (g : Fin ρ → Option (Fin (2 ^ b))) (i : Fin ρ)
    (hi : g i = none) :
    ∑ u : Fin (2 ^ b), partialSmallSumCount ρ b (Function.update g i (some u)) S
      = partialSmallSumCount ρ b g S := by
  classical
  rw [partialSmallSumCount, Finset.card_eq_sum_card_fiberwise
    (f := fun v : Fin ρ → Fin (2 ^ b) => v i) (t := Finset.univ)
    (fun v _ => Finset.mem_univ _)]
  refine (Finset.sum_congr rfl fun u _ => ?_).symm
  rw [partialSmallSumCount, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  constructor
  · rintro ⟨⟨hext, hsum⟩, hvi⟩
    refine ⟨fun j h hj => ?_, hsum⟩
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self] at hj
      cases hj
      exact hvi
    · rw [Function.update_of_ne hji] at hj
      exact hext j h hj
  · rintro ⟨hext, hsum⟩
    have hvi : v i = u := hext i u (by rw [Function.update_self])
    refine ⟨⟨fun j h hj => ?_, hsum⟩, hvi⟩
    by_cases hji : j = i
    · subst hji; rw [hi] at hj; cases hj
    · exact hext j h (by rw [Function.update_of_ne hji]; exact hj)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Revealing a fresh coordinate decreases the miss count by exactly one. -/
private lemma missCard_update {ρ' b' : ℕ} (g : Fin ρ' → Option (Fin (2 ^ b'))) (i : Fin ρ')
    (u : Fin (2 ^ b')) (hi : g i = none) :
    missCard g = missCard (Function.update g i (some u)) + 1 := by
  classical
  unfold missCard
  have hset : (Finset.univ.filter fun j : Fin ρ' => Function.update g i (some u) j = none)
      = (Finset.univ.filter fun j : Fin ρ' => g j = none).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    by_cases hji : j = i
    · subst hji; simp [Function.update_self]
    · simp [hji]
  have hmem : i ∈ Finset.univ.filter fun j : Fin ρ' => g j = none :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [hset, Finset.card_erase_of_mem hmem]
  have hpos : 0 < (Finset.univ.filter fun j : Fin ρ' => g j = none).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Fresh slot = μ.** The potential of an untouched slot is exactly
`smallSumCount ρ b S / (2^b)^ρ`. -/
private lemma slotPsi_none :
    slotPsi ρ b S (fun _ => none)
      = (smallSumCount ρ b S : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) ^ ρ := by
  unfold slotPsi
  rw [partialSmallSumCount_none ρ b S]
  congr 1
  simp [missCard]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Tower identity.** Averaging the slot potential over a uniformly revealed fresh
coordinate recovers the current slot potential: the per-slot potential is a martingale under
revealing one coordinate. With `g = fun _ => none` this is the open-step identity. -/
private lemma slotPsi_tower (g : Fin ρ → Option (Fin (2 ^ b))) (i : Fin ρ) (hi : g i = none) :
    (∑ u : Fin (2 ^ b), slotPsi ρ b S (Function.update g i (some u)))
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = slotPsi ρ b S g := by
  classical
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmem : i ∈ Finset.univ.filter fun j : Fin ρ => g j = none :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have h1 : 1 ≤ missCard g := Finset.card_pos.mpr ⟨i, hmem⟩
  have hmiss : ∀ u : Fin (2 ^ b),
      missCard (Function.update g i (some u)) = missCard g - 1 := by
    intro u
    have := missCard_update g i u hi
    omega
  have hm : missCard g - 1 + 1 = missCard g := by omega
  unfold slotPsi
  simp only [hmiss, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_partialSmallSumCount_update ρ b S g i hi,
    mul_assoc,
    ← ENNReal.mul_inv (Or.inl (pow_ne_zero _ hD0)) (Or.inl (ENNReal.pow_ne_top hDtop)),
    ← pow_succ, hm]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each extending tuple is determined by its values on the unrevealed coordinates, so the
partial count is at most `(2^b)^missCard g`. -/
private lemma partialSmallSumCount_le_pow (g : Fin ρ → Option (Fin (2 ^ b))) :
    partialSmallSumCount ρ b g S ≤ (2 ^ b) ^ missCard g := by
  classical
  have hle : partialSmallSumCount ρ b g S
      ≤ Fintype.card
          ({j // j ∈ Finset.univ.filter fun j : Fin ρ => g j = none} → Fin (2 ^ b)) := by
    rw [partialSmallSumCount, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun v j => v j.1) (fun v _ => Finset.mem_univ _) ?_
    intro v hv w hw hvw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    funext j
    by_cases hj : g j = none
    · exact congrFun hvw ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    · obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hj
      rw [hv.1 j h hh, hw.1 j h hh]
  refine hle.trans (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, missCard]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- The slot potential is a probability: `slotPsi ρ b S g ≤ 1`. -/
private lemma slotPsi_le_one (g : Fin ρ → Option (Fin (2 ^ b))) : slotPsi ρ b S g ≤ 1 := by
  unfold slotPsi
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc (partialSmallSumCount ρ b g S : ℝ≥0∞)
      ≤ (((2 ^ b) ^ missCard g : ℕ) : ℝ≥0∞) :=
        Nat.cast_le.mpr (partialSmallSumCount_le_pow ρ b S g)
    _ = ((2 ^ b : ℕ) : ℝ≥0∞) ^ missCard g := by push_cast; rfl

/-- Update one coordinate of one slot of a multi-slot state. -/
private def updateSlot {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) : K → Fin ρ' → Option (Fin (2 ^ b')) :=
  Function.update st k₀ (Function.update (st k₀) i₀ (some u))

/-- Multi-slot potential: the sum of the live slots' potentials over the touched keys. -/
private noncomputable def Phi (ρ b S : ℕ) {K : Type} (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b))) (dead : K → Prop) [DecidablePred dead] : ℝ≥0∞ :=
  ∑ k ∈ keys, if dead k then 0 else slotPsi ρ b S (st k)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma updateSlot_apply_ne {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) {k : K} (hk : k ≠ k₀) : updateSlot st k₀ i₀ u k = st k :=
  Function.update_of_ne hk _ _

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma updateSlot_apply_self {ρ' b' : ℕ} {K : Type} [DecidableEq K]
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) (k₀ : K) (i₀ : Fin ρ')
    (u : Fin (2 ^ b')) : updateSlot st k₀ i₀ u k₀ = Function.update (st k₀) i₀ (some u) :=
  Function.update_self _ _ _

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Extend = martingale.** Querying a fresh coordinate of a live, already-open slot leaves
the expected potential unchanged. -/
private lemma Phi_extend {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∈ keys) (hdead : ¬dead k₀) (hi : st k₀ i₀ = none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S keys (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = Phi ρ b S keys st dead := by
  classical
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : ∀ u : Fin (2 ^ b),
      Phi ρ b S keys (updateSlot st k₀ i₀ u) dead
        = slotPsi ρ b S (Function.update (st k₀) i₀ (some u))
          + ∑ k ∈ keys.erase k₀, if dead k then 0 else slotPsi ρ b S (st k) := by
    intro u
    rw [Phi, ← Finset.add_sum_erase _ _ hk, if_neg hdead, updateSlot_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [updateSlot_apply_ne st k₀ i₀ u (Finset.ne_of_mem_erase hk')]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, ENNReal.add_div, slotPsi_tower ρ b S (st k₀) i₀ hi,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right hD0 hDtop, Phi, ← Finset.add_sum_erase _ _ hk,
    if_neg hdead]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Open, live case (equality).** Opening a fresh slot at a live key adds exactly
`μ = slotPsi ρ b S (fun _ => none)` to the expected potential. Requires the slot's state to be
untouched (`hfresh`) — exactly the invariant that untouched keys carry all-`none` states. -/
private lemma Phi_open_eq {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∉ keys) (hdead : ¬dead k₀) (hfresh : st k₀ = fun _ => none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      = Phi ρ b S keys st dead + slotPsi ρ b S (fun _ => none) := by
  classical
  have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
  have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : ∀ u : Fin (2 ^ b),
      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead
        = slotPsi ρ b S (Function.update (st k₀) i₀ (some u)) + Phi ρ b S keys st dead := by
    intro u
    rw [Phi, Finset.sum_insert hk, if_neg hdead, updateSlot_apply_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [updateSlot_apply_ne st k₀ i₀ u (fun h => hk (h ▸ hk'))]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, ENNReal.add_div,
    slotPsi_tower ρ b S (st k₀) i₀ (by rw [hfresh]), hfresh,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
    ENNReal.mul_div_cancel_right hD0 hDtop, add_comm]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Open, general case (inequality).** Opening a fresh slot adds at most `μ` to the
expected potential (a dead key contributes nothing). -/
private lemma Phi_open_le {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∉ keys) (hfresh : st k₀ = fun _ => none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ Phi ρ b S keys st dead + slotPsi ρ b S (fun _ => none) := by
  classical
  by_cases hdead : dead k₀
  · have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
    have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hsplit : ∀ u : Fin (2 ^ b),
        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) dead
          = Phi ρ b S keys st dead := by
      intro u
      rw [Phi, Finset.sum_insert hk, if_pos hdead, zero_add]
      refine Finset.sum_congr rfl fun k hk' => ?_
      rw [updateSlot_apply_ne st k₀ i₀ u (fun h => hk (h ▸ hk'))]
    simp only [hsplit]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right hD0 hDtop]
    exact le_self_add
  · exact le_of_eq (Phi_open_eq ρ b S keys st dead k₀ i₀ hk hdead hfresh)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Kill.** Any step that only grows the dead set (state and keys unchanged) can only
decrease the potential. -/
private lemma Phi_mono_dead {K : Type} (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead dead' : K → Prop) [DecidablePred dead] [DecidablePred dead']
    (h : ∀ k, dead k → dead' k) :
    Phi ρ b S keys st dead' ≤ Phi ρ b S keys st dead := by
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : dead' k
  · simp [hk]
  · rw [if_neg hk, if_neg fun hd => hk (h k hd)]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Extend, deadness-agnostic (inequality).** Querying a fresh coordinate of an already-open
slot cannot increase the expected potential, whether or not the key is dead. -/
private lemma Phi_extend_le {K : Type} [DecidableEq K] (keys : Finset K)
    (st : K → Fin ρ → Option (Fin (2 ^ b)))
    (dead : K → Prop) [DecidablePred dead] (k₀ : K) (i₀ : Fin ρ)
    (hk : k₀ ∈ keys) (hi : st k₀ i₀ = none) :
    (∑ u : Fin (2 ^ b), Phi ρ b S keys (updateSlot st k₀ i₀ u) dead)
        / ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ Phi ρ b S keys st dead := by
  classical
  by_cases hdead : dead k₀
  · have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
    have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hconst : ∀ u : Fin (2 ^ b),
        Phi ρ b S keys (updateSlot st k₀ i₀ u) dead = Phi ρ b S keys st dead := by
      intro u
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkk : k = k₀
      · subst hkk; simp [hdead]
      · rw [updateSlot_apply_ne st k₀ i₀ u hkk]
    simp only [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
      ENNReal.mul_div_cancel_right hD0 hDtop]
  · exact le_of_eq (Phi_extend ρ b S keys st dead k₀ i₀ hk hdead hi)

/-- Expected payoff of a probabilistic computation against a nonnegative payoff function. -/
private noncomputable def EP {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, Pr[= x | mx] * f x

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma EP_pure {α : Type} (x : α) (f : α → ℝ≥0∞) :
    EP (pure x : ProbComp α) f = f x := by
  unfold EP
  rw [tsum_eq_single x]
  · rw [probOutput_pure_self, one_mul]
  · intro y hy
    rw [probOutput_pure_eq_indicator]
    simp [Set.indicator, hy]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma EP_bind {α β : Type} (mx : ProbComp α) (my : α → ProbComp β) (f : β → ℝ≥0∞) :
    EP (mx >>= my) f = ∑' x, Pr[= x | mx] * EP (my x) f := by
  unfold EP
  calc ∑' y, Pr[= y | mx >>= my] * f y
      = ∑' y, ∑' x, Pr[= x | mx] * Pr[= y | my x] * f y := by
        refine tsum_congr fun y => ?_
        rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, Pr[= x | mx] * Pr[= y | my x] * f y := ENNReal.tsum_comm
    _ = ∑' x, Pr[= x | mx] * ∑' y, Pr[= y | my x] * f y := by
        refine tsum_congr fun x => ?_
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
private lemma EP_bind_le_const {α β : Type} {mx : ProbComp α} {my : α → ProbComp β}
    {f : β → ℝ≥0∞} {C : ℝ≥0∞} (h : ∀ x, EP (my x) f ≤ C) :
    EP (mx >>= my) f ≤ C := by
  rw [EP_bind]
  calc ∑' x, Pr[= x | mx] * EP (my x) f
      ≤ ∑' x, Pr[= x | mx] * C := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = (∑' x, Pr[= x | mx]) * C := ENNReal.tsum_mul_right
    _ ≤ 1 * C := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = C := one_mul C

/-- The lazy random-oracle simulation for a constant-range hash spec: forward `unifSpec`
queries, lazily sample-and-cache hash queries. Abstract analogue of `fischlinImpl`. -/
@[reducible] private noncomputable def roImpl (b' : ℕ) (T : Type) [DecidableEq T] :
    QueryImpl (unifSpec + (T →ₒ Fin (2 ^ b')))
      (StateT (T →ₒ Fin (2 ^ b')).QueryCache ProbComp) :=
  unifFwdImpl (T →ₒ Fin (2 ^ b')) + randomOracle (spec := T →ₒ Fin (2 ^ b'))

/-- **Coupling invariant** between the random-oracle cache and the ghost slot state of the
supermartingale induction.

* `cached_iff`: the slot state is exactly the cache transported along `(key, coord)`
  (well-defined when `(key, coord)` is injective).
* `untouched`: keys outside `keys` carry the all-`none` slot state. -/
private structure INV (ρ' b' : ℕ) {T K : Type} (key : T → K) (coord : T → Fin ρ')
    (cache : (T →ₒ Fin (2 ^ b')).QueryCache) (keys : Finset K)
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) : Prop where
  cached_iff : ∀ (t : T) (u : Fin (2 ^ b')),
    cache t = some u ↔ st (key t) (coord t) = some u
  untouched : ∀ k ∉ keys, st k = fun _ => none

namespace INV

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- A cache miss at `s` means the corresponding slot coordinate is unrevealed. -/
private lemma slot_none {ρ' b' : ℕ} {T K : Type} {key : T → K} {coord : T → Fin ρ'}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV ρ' b' key coord cache keys st) {s : T}
    (hs : cache s = none) : st (key s) (coord s) = none := by
  cases h : st (key s) (coord s) with
  | none => rfl
  | some u =>
      have hc := (hINV.cached_iff s u).mpr h
      rw [hs] at hc
      exact absurd hc (by simp)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Invariant preservation at a cache miss.** Caching a fresh record `s ↦ u` updates the
ghost state by writing `u` into slot `key s`, coordinate `coord s`, and marking `key s`
as touched. -/
private lemma cacheQuery {ρ' b' : ℕ} {T K : Type} [DecidableEq T] [DecidableEq K]
    {key : T → K} {coord : T → Fin ρ'}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hinj : ∀ t₁ t₂, key t₁ = key t₂ → coord t₁ = coord t₂ → t₁ = t₂)
    (hINV : INV ρ' b' key coord cache keys st) (s : T) (hs : cache s = none)
    (u : Fin (2 ^ b')) :
    INV ρ' b' key coord (cache.cacheQuery s u) (insert (key s) keys)
      (updateSlot st (key s) (coord s) u) := by
  constructor
  · intro t' u'
    by_cases hts : t' = s
    · subst hts
      rw [QueryCache.cacheQuery_self, updateSlot_apply_self, Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hts]
      by_cases hkey : key t' = key s
      · have hcoord : coord t' ≠ coord s := fun hc => hts (hinj t' s hkey hc)
        rw [hkey, updateSlot_apply_self, Function.update_of_ne hcoord, ← hkey]
        exact hINV.cached_iff t' u'
      · rw [updateSlot_apply_ne st _ _ u hkey]
        exact hINV.cached_iff t' u'
  · intro k hk
    have hk1 : k ≠ key s := fun h => hk (h ▸ Finset.mem_insert_self _ _)
    have hk2 : k ∉ keys := fun h => hk (Finset.mem_insert_of_mem h)
    rw [updateSlot_apply_ne st _ _ u hk1]
    exact hINV.untouched k hk2

end INV

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **The main supermartingale induction.** Running `oa` under the lazy random-oracle
simulation from any cache coupled (via `INV`) to ghost state `(keys, st)`, the expected
terminal payoff is at most `q·μ + Φ + μ`, where `μ = slotPsi ρ b S (fun _ => none)` is the
untouched-slot potential, `Φ` is the current multi-slot potential, and `q` bounds the number
of hash queries.

* Each cache hit / `unifSpec` query leaves the potential unchanged.
* Each cache miss is a martingale step on an open slot (`Phi_extend_le`) or opens a fresh
  slot, paying `+μ` once per query (`Phi_open_le`) — telescoping into the `q·μ` term.
* The final `+μ` pays for the one extra slot the consumer's leaf may inspect (the proof's
  own `comList` slot, possibly never queried). -/
private theorem main_induction {T K : Type} [DecidableEq T]
    (key : T → K) (coord : T → Fin ρ)
    (hinj : ∀ t₁ t₂, key t₁ = key t₂ → coord t₁ = coord t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st, INV ρ b key coord cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α) :
    ∀ (q : ℕ), IsQueryBoundP oa (· matches .inr _) q →
    ∀ cache keys st, INV ρ b key coord cache keys st →
    EP ((simulateQ (roImpl b T) oa).run cache) (fun z => leaf z.1 z.2)
      ≤ (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
        + Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache keys st hINV
      rw [simulateQ_pure, StateT.run_pure, EP_pure]
      exact (hleaf x cache keys st hINV).trans (add_le_add le_add_self le_rfl)
  | query_bind t mx ih =>
      intro q hq cache keys st hINV
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hrest⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      rcases t with n | s
      · -- unifSpec query: forwarded, cache unchanged, budget unchanged
        have hbud : (if (Sum.inl n : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q :=
          if_neg (by simp)
        rw [hbud] at hrest
        change EP ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        have hrun : ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2)
            = (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>=
              fun a => (simulateQ (roImpl b T) (mx a)).run cache := by
          simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
          rw [OracleComp.liftM_run_StateT, bind_assoc]
          simp only [pure_bind]
        rw [hrun]
        exact EP_bind_le_const fun a => ih a q (hrest a) cache keys st hINV
      · -- hash query
        have hp : ((Sum.inr s : ℕ ⊕ T) matches Sum.inr _) := rfl
        have hq0 : 0 < q := hcan.resolve_left (by simp)
        have hbud : (if (Sum.inr s : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q - 1 :=
          if_pos hp
        rw [hbud] at hrest
        have hμ : ((q - 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
            + slotPsi ρ b S (fun _ => none)
            = (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
          have hcast : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
            exact_mod_cast Nat.succ_pred_eq_of_pos hq0
          rw [← hcast, add_mul, one_mul]
        change EP ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
            fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        rcases hc : cache s with _ | u
        · -- cache miss: fresh uniform sample, potential step
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = ($ᵗ Fin (2 ^ b)) >>= fun u =>
                  (simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u) := by
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, bind_map_left]
            rfl
          rw [hrun]
          set μ := slotPsi ρ b S (fun _ => none) with hμdef
          set k₀ := key s with hk₀
          set i₀ := coord s with hi₀
          have hIH : ∀ u : Fin (2 ^ b),
              EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                  (fun z => leaf z.1 z.2)
                ≤ ((q - 1 : ℕ) : ℝ≥0∞) * μ
                  + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ := by
            intro u
            refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) (insert k₀ keys)
              (updateSlot st k₀ i₀ u) (hINV.cacheQuery hinj s hc u)).trans ?_
            exact add_le_add (add_le_add le_rfl
              (Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u))) le_rfl
          have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
            Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
          have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          rw [EP_bind]
          calc ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                  * EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                      (fun z => leaf z.1 z.2)
              ≤ ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                  * (((q - 1 : ℕ) : ℝ≥0∞) * μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ) :=
                ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (hIH u)
            _ = ∑ u : Fin (2 ^ b), ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                  * (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                rw [tsum_fintype]
                refine Finset.sum_congr rfl fun u _ => ?_
                rw [probOutput_uniformSample, Fintype.card_fin, add_right_comm]
            _ = ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                  * ((2 ^ b) • (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                    + ∑ u : Fin (2 ^ b),
                        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
                  Finset.card_univ, Fintype.card_fin]
            _ = (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                  + (∑ u : Fin (2 ^ b),
                      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                    / ((2 ^ b : ℕ) : ℝ≥0∞) := by
                rw [mul_add, nsmul_eq_mul, ← mul_assoc,
                  ENNReal.inv_mul_cancel hD0 hDtop, one_mul, mul_comm
                    (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹, ← div_eq_mul_inv]
            _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := ?_
          rw [hμ]
          by_cases hkmem : k₀ ∈ keys
          · -- extend an already-open slot: martingale step
            rw [Finset.insert_eq_self.mpr hkmem]
            have hstep := Phi_extend_le ρ b S keys st (dead cache) k₀ i₀ hkmem
              (hINV.slot_none hc)
            calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                    Phi ρ b S keys (updateSlot st k₀ i₀ u) (dead cache))
                    / ((2 ^ b : ℕ) : ℝ≥0∞)
                ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) :=
                  add_le_add le_rfl hstep
              _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := le_self_add
          · -- open a fresh slot: pay one μ
            have hstep := Phi_open_le ρ b S keys st (dead cache) k₀ i₀ hkmem
              (hINV.untouched k₀ hkmem)
            calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                    Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                    / ((2 ^ b : ℕ) : ℝ≥0∞)
                ≤ (q : ℝ≥0∞) * μ + (Phi ρ b S keys st (dead cache) + μ) :=
                  add_le_add le_rfl hstep
              _ = (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := by
                  rw [add_assoc]
        · -- cache hit: no sampling, state unchanged, budget decremented
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = (simulateQ (roImpl b T) (mx u)).run cache := by
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, pure_bind]
          rw [hrun]
          refine (ih u (q - 1) (hrest u) cache keys st hINV).trans ?_
          exact add_le_add (add_le_add (mul_le_mul'
            (Nat.cast_le.mpr (Nat.sub_le q 1)) le_rfl) le_rfl) le_rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Initial-state specialization.** From the empty cache with no touched keys (`Φ = 0`),
the expected leaf payoff telescopes to exactly `(q + 1) · μ` — the
`(Q + 1) · smallSumCount / (2^b)^ρ` headline constant of `knowledgeSoundness_badEvent_le`
(via `slotPsi_none`). -/
private theorem main_induction_init {T K : Type} [DecidableEq T]
    (key : T → K) (coord : T → Fin ρ)
    (hinj : ∀ t₁ t₂, key t₁ = key t₂ → coord t₁ = coord t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st, INV ρ b key coord cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α)
    (q : ℕ) (hq : IsQueryBoundP oa (· matches .inr _) q) :
    EP ((simulateQ (roImpl b T) oa).run ∅) (fun z => leaf z.1 z.2)
      ≤ ((q + 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
  classical
  have hINV : INV ρ b key coord ∅ (∅ : Finset K) (fun _ _ => none) :=
    ⟨fun t u => by rw [QueryCache.empty_apply], fun _ _ => rfl⟩
  refine (main_induction ρ b S key coord hinj dead hdead_mono leaf hleaf oa q hq
    ∅ ∅ (fun _ _ => none) hINV).trans (le_of_eq ?_)
  rw [Phi, Finset.sum_empty, add_zero, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Weakened coupling invariant for the multi-record setting, relative to the deadness
predicate `dd` of the current cache. Unlike `INV`, the cache→state direction is restricted
to relevant records at live slots, and the state→cache direction only requires *some*
relevant record witnessing each revealed cell. -/
private structure INV' (ρ' b' : ℕ) {T K : Type} (relevant : T → Prop) (key : T → K)
    (coord : T → Fin ρ') (dd : K → Prop)
    (cache : (T →ₒ Fin (2 ^ b')).QueryCache) (keys : Finset K)
    (st : K → Fin ρ' → Option (Fin (2 ^ b'))) : Prop where
  cached_imp : ∀ (t : T) (u : Fin (2 ^ b')), relevant t → ¬ dd (key t) →
    cache t = some u → st (key t) (coord t) = some u
  revealed_has_record : ∀ (k : K) (i : Fin ρ') (u : Fin (2 ^ b')), ¬ dd k →
    st k i = some u → ∃ t, relevant t ∧ key t = k ∧ coord t = i ∧ cache t = some u
  untouched : ∀ k ∉ keys, st k = fun _ => none

namespace INV'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Inert step.** Caching a record that is irrelevant, or whose slot is (or becomes)
dead, preserves `INV'` with the ghost state unchanged. Covers the irrelevant, already-dead,
and kill cases of the generalized induction. -/
private lemma cacheQuery_inert {ρ' b' : ℕ} {T K : Type} [DecidableEq T]
    {relevant : T → Prop} {key : T → K} {coord : T → Fin ρ'} {dd dd' : K → Prop}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV' ρ' b' relevant key coord dd cache keys st)
    (hmono : ∀ k, dd k → dd' k)
    (s : T) (hs : cache s = none) (u : Fin (2 ^ b'))
    (hinert : relevant s → dd' (key s)) :
    INV' ρ' b' relevant key coord dd' (cache.cacheQuery s u) keys st := by
  constructor
  · intro t u₀ hrel hlive hcache
    by_cases hts : t = s
    · subst hts
      exact absurd (hinert hrel) hlive
    · rw [QueryCache.cacheQuery_of_ne _ _ hts] at hcache
      exact hINV.cached_imp t u₀ hrel (fun hd => hlive (hmono _ hd)) hcache
  · intro k i u₀ hlive hst
    obtain ⟨t, htrel, htk, hti, htc⟩ :=
      hINV.revealed_has_record k i u₀ (fun hd => hlive (hmono _ hd)) hst
    have hts : t ≠ s := fun h => by rw [h, hs] at htc; simp at htc
    exact ⟨t, htrel, htk, hti, by
      rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
  · exact hINV.untouched

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Reveal step.** Caching a relevant record at a fresh cell updates the ghost state by
writing the sampled value into the cell and marking the key as touched, preserving `INV'`. -/
private lemma cacheQuery_reveal {ρ' b' : ℕ} {T K : Type} [DecidableEq T] [DecidableEq K]
    {relevant : T → Prop} {key : T → K} {coord : T → Fin ρ'} {dd dd' : K → Prop}
    {cache : (T →ₒ Fin (2 ^ b')).QueryCache} {keys : Finset K}
    {st : K → Fin ρ' → Option (Fin (2 ^ b'))}
    (hINV : INV' ρ' b' relevant key coord dd cache keys st)
    (hmono : ∀ k, dd k → dd' k)
    (s : T) (hs : cache s = none) (hrel : relevant s)
    (hstn : st (key s) (coord s) = none) (u : Fin (2 ^ b')) :
    INV' ρ' b' relevant key coord dd' (cache.cacheQuery s u) (insert (key s) keys)
      (updateSlot st (key s) (coord s) u) := by
  constructor
  · intro t u₀ htrel hlive hcache
    by_cases hts : t = s
    · subst hts
      rw [QueryCache.cacheQuery_self] at hcache
      rw [updateSlot_apply_self, Function.update_self]
      exact hcache
    · rw [QueryCache.cacheQuery_of_ne _ _ hts] at hcache
      have hold := hINV.cached_imp t u₀ htrel (fun hd => hlive (hmono _ hd)) hcache
      by_cases hkey : key t = key s
      · by_cases hcoord : coord t = coord s
        · exfalso
          rw [hkey, hcoord, hstn] at hold
          simp at hold
        · rw [hkey, updateSlot_apply_self, Function.update_of_ne hcoord, ← hkey]
          exact hold
      · rw [updateSlot_apply_ne st _ _ u hkey]
        exact hold
  · intro k i u₀ hlive hst
    by_cases hk : k = key s
    · subst hk
      by_cases hi : i = coord s
      · subst hi
        rw [updateSlot_apply_self, Function.update_self] at hst
        refine ⟨s, hrel, rfl, rfl, ?_⟩
        rw [QueryCache.cacheQuery_self]
        exact hst
      · rw [updateSlot_apply_self, Function.update_of_ne hi] at hst
        obtain ⟨t, htrel, htk, hti, htc⟩ :=
          hINV.revealed_has_record (key s) i u₀ (fun hd => hlive (hmono _ hd)) hst
        have hts : t ≠ s := fun h => hi (by rw [← hti, h])
        exact ⟨t, htrel, htk, hti, by
          rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
    · rw [updateSlot_apply_ne st _ _ u hk] at hst
      obtain ⟨t, htrel, htk, hti, htc⟩ :=
        hINV.revealed_has_record k i u₀ (fun hd => hlive (hmono _ hd)) hst
      have hts : t ≠ s := fun h => hk (by rw [← htk, h])
      exact ⟨t, htrel, htk, hti, by
        rw [QueryCache.cacheQuery_of_ne _ _ hts]; exact htc⟩
  · intro k hk
    have hk1 : k ≠ key s := fun h => hk (h ▸ Finset.mem_insert_self _ _)
    have hk2 : k ∉ keys := fun h => hk (Finset.mem_insert_of_mem h)
    rw [updateSlot_apply_ne st _ _ u hk1]
    exact hINV.untouched k hk2

end INV'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **The generalized supermartingale induction (multi-record cells).** As
`main_induction`, but instead of joint injectivity of `(key, coord)`, only the *relevant*
records matter, and within a cell relevant records are separated by an abstract challenge
tag `chalOf` (`hcell`). Caching a second relevant record at an already-revealed cell kills
the slot (`hdead_kill`); all other relevant/live cache misses are martingale reveal steps;
irrelevant and dead-slot misses leave the potential unchanged. The bound is unchanged:
`q·μ + Φ + μ`. -/
private theorem main_induction_gen {T K C : Type} [DecidableEq T]
    (relevant : T → Prop)
    (key : T → K) (coord : T → Fin ρ) (chalOf : T → C)
    (hcell : ∀ t₁ t₂, relevant t₁ → relevant t₂ → key t₁ = key t₂ → coord t₁ = coord t₂ →
      chalOf t₁ = chalOf t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    (hdead_kill : ∀ (cache : (T →ₒ Fin (2 ^ b)).QueryCache) (t t' : T) (u u' : Fin (2 ^ b)),
      relevant t → relevant t' → key t = key t' → coord t = coord t' →
      chalOf t ≠ chalOf t' → cache t' = some u' → dead (cache.cacheQuery t u) (key t))
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st,
      INV' ρ b relevant key coord (dead cache) cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α) :
    ∀ (q : ℕ), IsQueryBoundP oa (· matches .inr _) q →
    ∀ cache keys st, INV' ρ b relevant key coord (dead cache) cache keys st →
    EP ((simulateQ (roImpl b T) oa).run cache) (fun z => leaf z.1 z.2)
      ≤ (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
        + Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q _ cache keys st hINV
      rw [simulateQ_pure, StateT.run_pure, EP_pure]
      exact (hleaf x cache keys st hINV).trans (add_le_add le_add_self le_rfl)
  | query_bind t mx ih =>
      intro q hq cache keys st hINV
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hrest⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      rcases t with n | s
      · -- unifSpec query: forwarded, cache unchanged, budget unchanged
        have hbud : (if (Sum.inl n : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q :=
          if_neg (by simp)
        rw [hbud] at hrest
        change EP ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        have hrun : ((unifFwdImpl (T →ₒ Fin (2 ^ b)) n).run cache >>=
            fun p : unifSpec.Range n × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2)
            = (HasQuery.query (spec := unifSpec) (m := ProbComp) n) >>=
              fun a => (simulateQ (roImpl b T) (mx a)).run cache := by
          simp only [unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
          rw [OracleComp.liftM_run_StateT, bind_assoc]
          simp only [pure_bind]
        rw [hrun]
        exact EP_bind_le_const fun a => ih a q (hrest a) cache keys st hINV
      · -- hash query
        have hp : ((Sum.inr s : ℕ ⊕ T) matches Sum.inr _) := rfl
        have hq0 : 0 < q := hcan.resolve_left (by simp)
        have hbud : (if (Sum.inr s : ℕ ⊕ T) matches Sum.inr _ then q - 1 else q) = q - 1 :=
          if_pos hp
        rw [hbud] at hrest
        have hμ : ((q - 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none)
            + slotPsi ρ b S (fun _ => none)
            = (q : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
          have hcast : ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
            exact_mod_cast Nat.succ_pred_eq_of_pos hq0
          rw [← hcast, add_mul, one_mul]
        change EP ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
            fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
              (simulateQ (roImpl b T) (mx p.1)).run p.2) (fun z => leaf z.1 z.2) ≤ _
        rcases hc : cache s with _ | u
        · -- cache miss: fresh uniform sample
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = ($ᵗ Fin (2 ^ b)) >>= fun u =>
                  (simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u) := by
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, bind_map_left]
            rfl
          rw [hrun]
          by_cases hlive : relevant s ∧ ¬ dead cache (key s) ∧ st (key s) (coord s) = none
          · -- REVEAL: relevant record at a fresh cell of a live slot — martingale step
            obtain ⟨hrel, hdd, hstn⟩ := hlive
            set μ := slotPsi ρ b S (fun _ => none) with hμdef
            set k₀ := key s with hk₀
            set i₀ := coord s with hi₀
            have hIH : ∀ u : Fin (2 ^ b),
                EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                    (fun z => leaf z.1 z.2)
                  ≤ ((q - 1 : ℕ) : ℝ≥0∞) * μ
                    + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ := by
              intro u
              refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) (insert k₀ keys)
                (updateSlot st k₀ i₀ u)
                (hINV.cacheQuery_reveal (hdead_mono cache s u) s hc hrel hstn u)).trans ?_
              exact add_le_add (add_le_add le_rfl
                (Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u))) le_rfl
            have hD0 : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ 0 :=
              Nat.cast_ne_zero.mpr (pow_ne_zero b two_ne_zero)
            have hDtop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
            rw [EP_bind]
            calc ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                    * EP ((simulateQ (roImpl b T) (mx u)).run (cache.cacheQuery s u))
                        (fun z => leaf z.1 z.2)
                ≤ ∑' u, Pr[= u | $ᵗ Fin (2 ^ b)]
                    * (((q - 1 : ℕ) : ℝ≥0∞) * μ
                      + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache) + μ) :=
                  ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (hIH u)
              _ = ∑ u : Fin (2 ^ b), ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                    * (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ
                      + Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                  rw [tsum_fintype]
                  refine Finset.sum_congr rfl fun u _ => ?_
                  rw [probOutput_uniformSample, Fintype.card_fin, add_right_comm]
              _ = ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
                    * ((2 ^ b) • (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                      + ∑ u : Fin (2 ^ b),
                          Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache)) := by
                  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
                    Finset.card_univ, Fintype.card_fin]
              _ = (((q - 1 : ℕ) : ℝ≥0∞) * μ + μ)
                    + (∑ u : Fin (2 ^ b),
                        Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞) := by
                  rw [mul_add, nsmul_eq_mul, ← mul_assoc,
                    ENNReal.inv_mul_cancel hD0 hDtop, one_mul, mul_comm
                      (((2 ^ b : ℕ) : ℝ≥0∞))⁻¹, ← div_eq_mul_inv]
              _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := ?_
            rw [hμ]
            by_cases hkmem : k₀ ∈ keys
            · -- extend an already-open slot: martingale step
              rw [show insert k₀ keys = keys from Finset.insert_eq_self.mpr hkmem]
              have hstep := Phi_extend_le ρ b S keys st (dead cache) k₀ i₀ hkmem hstn
              calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                      Phi ρ b S keys (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞)
                  ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) :=
                    add_le_add le_rfl hstep
                _ ≤ (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := le_self_add
            · -- open a fresh slot: pay one μ
              have hstep := Phi_open_le ρ b S keys st (dead cache) k₀ i₀ hkmem
                (hINV.untouched k₀ hkmem)
              calc (q : ℝ≥0∞) * μ + (∑ u : Fin (2 ^ b),
                      Phi ρ b S (insert k₀ keys) (updateSlot st k₀ i₀ u) (dead cache))
                      / ((2 ^ b : ℕ) : ℝ≥0∞)
                  ≤ (q : ℝ≥0∞) * μ + (Phi ρ b S keys st (dead cache) + μ) :=
                    add_le_add le_rfl hstep
                _ = (q : ℝ≥0∞) * μ + Phi ρ b S keys st (dead cache) + μ := by
                    rw [add_assoc]
          · -- INERT: irrelevant record, dead slot, or kill — ghost state unchanged,
            -- potential non-increasing, average over the sampled value is trivial.
            have hinert : ∀ u : Fin (2 ^ b),
                relevant s → dead (cache.cacheQuery s u) (key s) := by
              intro u hrel
              by_cases hdd : dead cache (key s)
              · exact hdead_mono cache s u _ hdd
              · rcases hcv : st (key s) (coord s) with _ | u'
                · exact absurd ⟨hrel, hdd, hcv⟩ hlive
                · -- KILL: the cell was revealed by an earlier relevant record `t'`;
                  -- by `hcell` its challenge tag differs, so `hdead_kill` applies.
                  obtain ⟨t', ht'rel, ht'k, ht'i, ht'c⟩ :=
                    hINV.revealed_has_record (key s) (coord s) u' hdd hcv
                  have hts : t' ≠ s := fun h => by
                    rw [h, hc] at ht'c; simp at ht'c
                  have hchal : chalOf s ≠ chalOf t' := fun h =>
                    hts.symm (hcell s t' hrel ht'rel ht'k.symm ht'i.symm h)
                  exact hdead_kill cache s t' u u' hrel ht'rel ht'k.symm ht'i.symm
                    hchal ht'c
            refine EP_bind_le_const fun u => ?_
            refine (ih u (q - 1) (hrest u) (cache.cacheQuery s u) keys st
              (hINV.cacheQuery_inert (hdead_mono cache s u) s hc u (hinert u))).trans ?_
            exact add_le_add (add_le_add
              (mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le q 1)) le_rfl)
              (Phi_mono_dead ρ b S _ _ _ _ (hdead_mono cache s u))) le_rfl
        · -- cache hit: no sampling, state unchanged, budget decremented
          have hrun : ((randomOracle (spec := T →ₒ Fin (2 ^ b)) s).run cache >>=
              fun p : Fin (2 ^ b) × (T →ₒ Fin (2 ^ b)).QueryCache =>
                (simulateQ (roImpl b T) (mx p.1)).run p.2)
              = (simulateQ (roImpl b T) (mx u)).run cache := by
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, pure_bind]
          rw [hrun]
          refine (ih u (q - 1) (hrest u) cache keys st hINV).trans ?_
          exact add_le_add (add_le_add (mul_le_mul'
            (Nat.cast_le.mpr (Nat.sub_le q 1)) le_rfl) le_rfl) le_rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Initial-state specialization of `main_induction_gen`: from the empty cache the
expected leaf payoff is at most `(q + 1)·μ`. -/
private theorem main_induction_gen_init {T K C : Type} [DecidableEq T]
    (relevant : T → Prop)
    (key : T → K) (coord : T → Fin ρ) (chalOf : T → C)
    (hcell : ∀ t₁ t₂, relevant t₁ → relevant t₂ → key t₁ = key t₂ → coord t₁ = coord t₂ →
      chalOf t₁ = chalOf t₂ → t₁ = t₂)
    (dead : (T →ₒ Fin (2 ^ b)).QueryCache → K → Prop)
    [∀ c, DecidablePred (dead c)]
    (hdead_mono : ∀ c (t : T) (u : Fin (2 ^ b)) k, dead c k → dead (c.cacheQuery t u) k)
    (hdead_kill : ∀ (cache : (T →ₒ Fin (2 ^ b)).QueryCache) (t t' : T) (u u' : Fin (2 ^ b)),
      relevant t → relevant t' → key t = key t' → coord t = coord t' →
      chalOf t ≠ chalOf t' → cache t' = some u' → dead (cache.cacheQuery t u) (key t))
    {α : Type} (leaf : α → (T →ₒ Fin (2 ^ b)).QueryCache → ℝ≥0∞)
    (hleaf : ∀ (a : α) cache keys st,
      INV' ρ b relevant key coord (dead cache) cache keys st →
      leaf a cache ≤ Phi ρ b S keys st (dead cache) + slotPsi ρ b S (fun _ => none))
    (oa : OracleComp (unifSpec + (T →ₒ Fin (2 ^ b))) α)
    (q : ℕ) (hq : IsQueryBoundP oa (· matches .inr _) q) :
    EP ((simulateQ (roImpl b T) oa).run ∅) (fun z => leaf z.1 z.2)
      ≤ ((q + 1 : ℕ) : ℝ≥0∞) * slotPsi ρ b S (fun _ => none) := by
  classical
  have hINV : INV' ρ b relevant key coord (dead ∅) ∅ (∅ : Finset K)
      (fun _ _ => none) := by
    refine ⟨fun t u _ _ hcc => ?_, fun k i u _ hst => ?_, fun _ _ => rfl⟩
    · rw [QueryCache.empty_apply] at hcc
      simp at hcc
    · simp at hst
  refine (main_induction_gen ρ b S relevant key coord chalOf hcell dead hdead_mono
    hdead_kill leaf hleaf oa q hq ∅ ∅ (fun _ _ => none) hINV).trans (le_of_eq ?_)
  rw [Phi, Finset.sum_empty, add_zero, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Left query on the logged stack: forwarded, no log, cache unchanged. Stated with the
mapped function's domain at the sum-spec `Range` type so keyed rewriting fires after
`simulateQ_bind`. -/
private lemma loggedImpl_run_run_inl {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    (i : unifSpec.Domain) (c : hashSpec.QueryCache) :
    (((idImplW hashSpec + loggedROW hashSpec) (Sum.inl i)).run).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inl i)) =>
          ((u, (∅ : QueryLog hashSpec)), c)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) i) := by
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the logged stack, cache hit: cached value, logged, cache unchanged. -/
private lemma loggedImpl_run_run_inr_some {ι : Type} {hashSpec : OracleSpec ι}
    [DecidableEq ι] [hashSpec.DecidableEq]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache}
    {u : hashSpec.Range j} (h : c j = some u) :
    (((idImplW hashSpec + loggedROW hashSpec) (Sum.inr j)).run).run c =
      pure (((u, ([⟨j, u⟩] : QueryLog hashSpec)), c) :
        ((unifSpec + hashSpec).Range (Sum.inr j) × QueryLog hashSpec) ×
          hashSpec.QueryCache) := by
  change ((loggedROW hashSpec j).run).run c = _
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_some _ h, pure_bind]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the logged stack, cache miss: sample, log, cache the value. -/
private lemma loggedImpl_run_run_inr_none {ι : Type} {hashSpec : OracleSpec ι}
    [DecidableEq ι] [hashSpec.DecidableEq]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache} (h : c j = none) :
    (((idImplW hashSpec + loggedROW hashSpec) (Sum.inr j)).run).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inr j)) =>
          ((u, ([⟨j, u⟩] : QueryLog hashSpec)), c.cacheQuery j u)) <$>
        ($ᵗ hashSpec.Range j) := by
  change ((loggedROW hashSpec j).run).run c = _
  rw [loggedROW, QueryImpl.run_withLogging_apply, StateT.run_bind,
    show hashSpec.randomOracle = QueryImpl.withCaching uniformSampleImpl from rfl,
    QueryImpl.withCaching_run_none _ h]
  rw [show uniformSampleImpl (spec := hashSpec) j = ($ᵗ hashSpec.Range j) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Left query on the unlogged stack: forwarded, cache unchanged. -/
private lemma unloggedImpl_run_inl {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    (i : unifSpec.Domain) (c : hashSpec.QueryCache) :
    ((unifFwdImpl hashSpec + hashSpec.randomOracle) (Sum.inl i)).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inl i)) => (u, c)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) i) := by
  change (unifFwdImpl hashSpec i).run c = _
  simp [unifFwdImpl, StateT.run_monadLift, bind_pure_comp]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the unlogged stack, cache hit. -/
private lemma unloggedImpl_run_inr_some {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache}
    {u : hashSpec.Range j} (h : c j = some u) :
    ((unifFwdImpl hashSpec + hashSpec.randomOracle) (Sum.inr j)).run c =
      pure ((u, c) : (unifSpec + hashSpec).Range (Sum.inr j) × hashSpec.QueryCache) :=
  QueryImpl.withCaching_run_some (so := uniformSampleImpl) h

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Right query on the unlogged stack, cache miss. -/
private lemma unloggedImpl_run_inr_none {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {j : hashSpec.Domain} {c : hashSpec.QueryCache} (h : c j = none) :
    ((unifFwdImpl hashSpec + hashSpec.randomOracle) (Sum.inr j)).run c =
      (fun (u : (unifSpec + hashSpec).Range (Sum.inr j)) =>
        (u, c.cacheQuery j u)) <$> ($ᵗ hashSpec.Range j) :=
  QueryImpl.withCaching_run_none (so := uniformSampleImpl) h

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Dropping the log.** Projecting away the query log from the logged run yields, as a
plain `ProbComp` term equality, the unlogged run. -/
private theorem dropLog_run_eq {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α) (cache : hashSpec.QueryCache) :
    (fun z => (z.1.1, z.2)) <$>
        ((simulateQ (idImplW hashSpec + loggedROW hashSpec) oa).run).run cache
      = (simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle) oa).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure, map_pure]
  | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', StateT.run_bind,
        StateT.run_map, map_bind]
      cases t with
      | inl i =>
          rw [loggedImpl_run_run_inl, unloggedImpl_run_inl]
          simp only [bind_map_left, Functor.map_map, Prod.map_fst, id_eq]
          exact bind_congr fun u => ih u cache
      | inr j =>
          cases hc : cache j with
          | some u =>
              rw [loggedImpl_run_run_inr_some hc, unloggedImpl_run_inr_some hc]
              simp only [pure_bind, Functor.map_map, Prod.map_fst, id_eq]
              exact ih u cache
          | none =>
              rw [loggedImpl_run_run_inr_none hc, unloggedImpl_run_inr_none hc]
              simp only [bind_map_left, Functor.map_map, Prod.map_fst, id_eq]
              exact bind_congr fun u => ih u (cache.cacheQuery j u)

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Reindexing an expected payoff along a `map`. -/
private lemma EP_map {α β : Type} (mx : ProbComp α) (g : α → β) (f : β → ℝ≥0∞) :
    EP (g <$> mx) f = EP mx (f ∘ g) := by
  rw [map_eq_bind_pure_comp, EP_bind]
  exact tsum_congr fun x => by rw [Function.comp_apply, EP_pure, Function.comp_apply]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Expected payoffs that ignore the log coincide between the logged and unlogged runs. -/
private theorem dropLog_EP {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α) (cache : hashSpec.QueryCache)
    (f : α → hashSpec.QueryCache → ℝ≥0∞) :
    EP (((simulateQ (idImplW hashSpec + loggedROW hashSpec) oa).run).run cache)
        (fun z => f z.1.1 z.2)
      = EP ((simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle) oa).run cache)
        (fun w => f w.1 w.2) := by
  rw [← dropLog_run_eq oa cache, EP_map]
  rfl

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Probabilities of events depending only on the value and the final cache agree between
the logged and the unlogged run. -/
private theorem dropLog_probEvent {ι : Type} {hashSpec : OracleSpec ι} [DecidableEq ι]
    [hashSpec.DecidableEq] [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]
    {α : Type} (oa : OracleComp (unifSpec + hashSpec) α) (cache : hashSpec.QueryCache)
    (p : α → hashSpec.QueryCache → Prop) :
    Pr[fun z => p z.1.1 z.2 |
        ((simulateQ (idImplW hashSpec + loggedROW hashSpec) oa).run).run cache]
      = Pr[fun w => p w.1 w.2 |
        (simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle) oa).run cache] := by
  rw [← dropLog_run_eq oa cache, probEvent_map]
  rfl

/-! ### Knowledge-Soundness Assembly: Classifier Instantiation

The supermartingale induction `main_induction_gen_init` is instantiated on the Fischlin
random-oracle records: a record is *relevant* (`ksRelevant`) when it carries the proof's
statement/message tags and σ-verifies against the commitment stored at its repetition
index in its own commitment list; cells are indexed by `(comList, rep)`; and a
commitment-list key dies (`ksDead`) once the cache holds two relevant records in the same
cell with distinct challenges — exactly the event in which the online extractor succeeds. -/

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Relevance classifier for the supermartingale induction: the record carries the proof's
statement and message tags, and its challenge–response pair σ-verifies against the
commitment stored at its repetition index of its own commitment list. -/
private def ksRelevant (x : Stmt) (msg : M)
    (t : FischlinROInput Stmt Commit Chal Resp ρ M) : Prop :=
  t.stmt = x ∧ t.msg = msg ∧
    ∃ c, t.comList[(t.rep : ℕ)]? = some c ∧ σ.verify x c t.chal t.resp = true

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Deadness classifier: a commitment-list key is dead once the cache holds two relevant
records at the same repetition with distinct challenges (the extractor's success event). -/
private def ksDead (x : Stmt) (msg : M)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (k : List Commit) : Prop :=
  ∃ t t' : FischlinROInput Stmt Commit Chal Resp ρ M, ∃ u u' : Fin (2 ^ b),
    ksRelevant σ ρ M x msg t ∧ ksRelevant σ ρ M x msg t' ∧
      t.comList = k ∧ t'.comList = k ∧ t.rep = t'.rep ∧ t.chal ≠ t'.chal ∧
      cache t = some u ∧ cache t' = some u'

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- **Cell injectivity.** Under unique responses, two relevant records in the same cell
(same commitment list and repetition) with the same challenge are equal: the commitment is
determined by the cell, and the response by unique responses. -/
private lemma ksRelevant_cell_inj (hur : σ.UniqueResponses) (x : Stmt) (msg : M)
    (t₁ t₂ : FischlinROInput Stmt Commit Chal Resp ρ M)
    (h₁ : ksRelevant σ ρ M x msg t₁) (h₂ : ksRelevant σ ρ M x msg t₂)
    (hk : t₁.comList = t₂.comList) (hi : t₁.rep = t₂.rep) (hc : t₁.chal = t₂.chal) :
    t₁ = t₂ := by
  obtain ⟨s₁, m₁, cl₁, r₁, ch₁, rp₁⟩ := t₁
  obtain ⟨s₂, m₂, cl₂, r₂, ch₂, rp₂⟩ := t₂
  obtain ⟨hs₁, hm₁, c₁, hc₁, hv₁⟩ := h₁
  obtain ⟨hs₂, hm₂, c₂, hc₂, hv₂⟩ := h₂
  dsimp only at hs₁ hm₁ hc₁ hv₁ hs₂ hm₂ hc₂ hv₂ hk hi hc
  subst hs₁ hm₁ hs₂ hm₂ hk hi hc
  cases Option.some.inj (hc₁.symm.trans hc₂)
  exact congrArg (FischlinROInput.mk _ _ _ _ _) (hur _ c₁ _ rp₁ rp₂ hv₁ hv₂)

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Deadness is monotone** under caching: a cache update never erases an entry. -/
private lemma ksDead_mono (x : Stmt) (msg : M)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (s : FischlinROInput Stmt Commit Chal Resp ρ M) (v : Fin (2 ^ b)) (k : List Commit)
    (h : ksDead σ ρ b M x msg cache k) :
    ksDead σ ρ b M x msg (cache.cacheQuery s v) k := by
  obtain ⟨t, t', u, u', h₁, h₂, h₃, h₄, h₅, h₆, hct, hct'⟩ := h
  have hsome : ∀ (r : FischlinROInput Stmt Commit Chal Resp ρ M) (w : Fin (2 ^ b)),
      cache r = some w → ∃ w', (cache.cacheQuery s v) r = some w' := by
    intro r w hw
    by_cases hrs : r = s
    · subst hrs
      exact ⟨v, QueryCache.cacheQuery_self cache r v⟩
    · exact ⟨w, by rw [QueryCache.cacheQuery_of_ne _ _ hrs]; exact hw⟩
  obtain ⟨w, hw⟩ := hsome t u hct
  obtain ⟨w', hw'⟩ := hsome t' u' hct'
  exact ⟨t, t', w, w', h₁, h₂, h₃, h₄, h₅, h₆, hw, hw'⟩

omit [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] in
/-- **Kill step.** Caching a relevant record on top of a cached relevant record in the same
cell with a different challenge makes the key dead. -/
private lemma ksDead_kill (x : Stmt) (msg : M)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (t t' : FischlinROInput Stmt Commit Chal Resp ρ M) (u u' : Fin (2 ^ b))
    (hrel : ksRelevant σ ρ M x msg t) (hrel' : ksRelevant σ ρ M x msg t')
    (hk : t.comList = t'.comList) (hi : t.rep = t'.rep) (hch : t.chal ≠ t'.chal)
    (hc' : cache t' = some u') :
    ksDead σ ρ b M x msg (cache.cacheQuery t u) t.comList := by
  have hne : t' ≠ t := fun h => hch (by rw [h])
  exact ⟨t, t', u, u', hrel, hrel', rfl, hk.symm, hi, hch,
    QueryCache.cacheQuery_self cache t u,
    by rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hc'⟩

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- Each per-repetition verification record of a σ-verifying proof is relevant. -/
private lemma ksRelevant_record (x : Stmt) (msg : M) (π : FischlinProof Commit Chal Resp ρ)
    (i : Fin ρ) (hver : σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true) :
    ksRelevant σ ρ M x msg
      ⟨x, msg, List.ofFn fun j => (π j).1, i, (π i).2.1, (π i).2.2⟩ := by
  refine ⟨rfl, rfl, (π i).1, ?_, hver⟩
  rw [List.getElem?_ofFn, dif_pos i.isLt]

omit [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal] [DecidableEq Resp]
  [FinEnum Chal] [Inhabited Chal] [Inhabited Resp] [SampleableType Chal] [DecidableEq M] in
/-- A relevant record at the proof's commitment list σ-verifies against the proof's
commitment at the record's repetition. -/
private lemma ksRelevant_verify_at (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ) (t : FischlinROInput Stmt Commit Chal Resp ρ M)
    (h : ksRelevant σ ρ M x msg t)
    (hcom : t.comList = List.ofFn fun j => (π j).1) :
    σ.verify x (π t.rep).1 t.chal t.resp = true := by
  obtain ⟨_, _, c, hc, hv⟩ := h
  rw [hcom, List.getElem?_ofFn, dif_pos t.rep.isLt] at hc
  cases Option.some.inj hc
  exact hv

omit [SampleableType Chal] in
/-- Leaf payoff of the knowledge-soundness induction: the acceptance probability of the
Fischlin verifier on the final cache, gated by the cache-side pinning predicate
`CachePinned` (the event that the extractor's log scan misses). -/
private noncomputable def ksLeaf (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache) : ℝ≥0∞ :=
  letI : Decidable (CachePinned σ ρ b M x π cache) := Classical.propDecidable _
  (if CachePinned σ ρ b M x π cache then 1 else 0) *
    Pr[= true | (simulateQ (fischlinImpl ρ b M)
      ((Fischlin (m := OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M))
        σ hr ρ b S M).verify x msg π)).run' cache]

omit [SampleableType Chal] in
/-- **Per-leaf bound.** Under the weakened coupling invariant `INV'` for the Fischlin
classifiers, the leaf payoff is at most the live multi-slot potential plus one fresh slot
potential: when the scan misses (`CachePinned`), the verifier's acceptance probability is
*exactly* the slot potential of the proof's commitment-list key, which is either a live
summand of `Phi` or (if untouched) exactly `μ`. -/
private lemma fischlin_leaf_le (hur : σ.UniqueResponses) (x : Stmt) (msg : M)
    (π : FischlinProof Commit Chal Resp ρ)
    (cache : (fischlinROSpec Stmt Commit Chal Resp ρ b M).QueryCache)
    (keys : Finset (List Commit))
    (st : List Commit → Fin ρ → Option (Fin (2 ^ b)))
    [DecidablePred (ksDead σ ρ b M x msg cache)]
    (hINV : INV' ρ b (ksRelevant σ ρ M x msg) (fun t => t.comList) (fun t => t.rep)
      (ksDead σ ρ b M x msg cache) cache keys st) :
    ksLeaf σ hr ρ b S M x msg π cache
      ≤ Phi ρ b S keys st (ksDead σ ρ b M x msg cache)
        + slotPsi ρ b S (fun _ => none) := by
  unfold ksLeaf
  by_cases hpin : CachePinned σ ρ b M x π cache
  case neg =>
    rw [if_neg hpin, zero_mul]
    exact zero_le'
  rw [if_pos hpin, one_mul]
  by_cases hver : ∀ i, σ.verify x (π i).1 (π i).2.1 (π i).2.2 = true
  case neg =>
    -- Some repetition fails σ-verification: acceptance probability is zero.
    have hall :
        ((List.finRange ρ).all fun i => σ.verify x (π i).1 (π i).2.1 (π i).2.2) ≠ true :=
      fun hAll => hver fun i => List.all_eq_true.mp hAll i (List.mem_finRange i)
    rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache
      (fun j => cache ⟨x, msg, List.ofFn fun k => (π k).1, j, (π j).2.1, (π j).2.2⟩)
      (fun j => rfl), if_neg hall, zero_mul, ENNReal.zero_div]
    exact zero_le'
  set k₀ : List Commit := List.ofFn fun j => (π j).1 with hk₀
  -- The proof's key is live: deadness would give two distinct pinned challenges in a cell.
  have hlive : ¬ ksDead σ ρ b M x msg cache k₀ := by
    rintro ⟨t, t', u, u', hrel, hrel', hck, hck', hrep, hchal, hct, hct'⟩
    have hpt : t.chal = (π t.rep).2.1 :=
      hpin t u hct hrel.1 hck (ksRelevant_verify_at σ ρ M x msg π t hrel hck)
    have hpt' : t'.chal = (π t'.rep).2.1 :=
      hpin t' u' hct' hrel'.1 hck' (ksRelevant_verify_at σ ρ M x msg π t' hrel' hck')
    exact hchal (by rw [hpt, hpt', hrep])
  -- Hits correspondence: the cache at the proof's records is exactly the ghost slot state.
  have hcache : ∀ i : Fin ρ,
      cache ⟨x, msg, k₀, i, (π i).2.1, (π i).2.2⟩ = st k₀ i := by
    intro i
    cases hc : cache ⟨x, msg, k₀, i, (π i).2.1, (π i).2.2⟩ with
    | some u =>
        exact (hINV.cached_imp _ u (ksRelevant_record σ ρ M x msg π i (hver i)) hlive hc).symm
    | none =>
        cases hst : st k₀ i with
        | none => rfl
        | some u =>
            exfalso
            obtain ⟨t, htrel, htk, hti, htc⟩ := hINV.revealed_has_record k₀ i u hlive hst
            have hchal : t.chal = (π t.rep).2.1 :=
              hpin t u htc htrel.1 htk (ksRelevant_verify_at σ ρ M x msg π t htrel htk)
            have hresp : t.resp = (π t.rep).2.2 :=
              hur x (π t.rep).1 (π t.rep).2.1 t.resp (π t.rep).2.2
                (hchal ▸ ksRelevant_verify_at σ ρ M x msg π t htrel htk) (hver t.rep)
            obtain ⟨hts, htm, -⟩ := htrel
            have ht : t = ⟨x, msg, k₀, i, (π i).2.1, (π i).2.2⟩ := by
              obtain ⟨ts, tm, tcl, tr, tch, trp⟩ := t
              dsimp only at hts htm htk hti hchal hresp
              subst hts htm htk hti
              rw [hchal, hresp]
            rw [ht, hc] at htc
            exact Option.some_ne_none u htc.symm
  -- Exact leaf value: the slot potential of the proof's key.
  have hall :
      ((List.finRange ρ).all fun i => σ.verify x (π i).1 (π i).2.1 (π i).2.2) = true :=
    List.all_eq_true.mpr fun i _ => hver i
  rw [verify_probOutput_true_mixed σ hr ρ b S M x msg π cache (st k₀) hcache, if_pos hall,
    one_mul]
  change slotPsi ρ b S (st k₀) ≤ _
  by_cases hk : k₀ ∈ keys
  · -- Touched live key: its slot potential is a summand of `Phi`.
    refine le_trans ?_ le_self_add
    rw [Phi]
    calc slotPsi ρ b S (st k₀)
        = if ksDead σ ρ b M x msg cache k₀ then 0 else slotPsi ρ b S (st k₀) :=
          (if_neg hlive).symm
      _ ≤ ∑ k ∈ keys, if ksDead σ ρ b M x msg cache k then 0 else slotPsi ρ b S (st k) :=
          Finset.single_le_sum
            (f := fun k => if ksDead σ ρ b M x msg cache k then 0 else slotPsi ρ b S (st k))
            (fun k _ => zero_le') hk
  · -- Untouched key: its slot state is all-`none`, contributing exactly `μ`.
    rw [hINV.untouched k₀ hk]
    exact le_add_self

omit [SampleableType Chal] in
/-- **Factoring the miss event through the logged run.** The probability that the verifier
accepts while the extractor's scan misses equals the expected value, over the logged prover
run, of the scan-miss indicator times the verifier's acceptance probability on the final
cache. -/
private lemma ksSample_probEvent_eq_EP
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    Pr[fun out => out.2 = true ∧ fischlinFindWitness σ ρ b M x out.1.1 out.1.2 = none
        | ksSample σ hr ρ b S M prover x msg]
      = EP (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅)
        (fun z =>
          (if fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none then 1 else 0) *
            Pr[= true | (simulateQ (fischlinImpl ρ b M)
              ((Fischlin (m := OracleComp (unifSpec
                  + fischlinROSpec Stmt Commit Chal Resp ρ b M))
                σ hr ρ b S M).verify x msg z.1.1)).run' z.2]) := by
  classical
  have hks : ksSample σ hr ρ b S M prover x msg
      = ((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅ >>= fun z =>
            (simulateQ (fischlinImpl ρ b M)
              ((Fischlin (m := OracleComp (unifSpec
                  + fischlinROSpec Stmt Commit Chal Resp ρ b M))
                σ hr ρ b S M).verify x msg z.1.1)).run z.2 >>= fun vc =>
              pure ((z.1.1, z.1.2), vc.1) := rfl
  rw [hks, probEvent_bind_eq_tsum, EP]
  refine tsum_congr fun z => ?_
  congr 1
  rw [probEvent_bind_eq_tsum]
  by_cases hfw : fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none
  · rw [if_pos hfw, one_mul, StateT.run', ← probEvent_eq_eq_probOutput, probEvent_map,
      probEvent_eq_tsum_ite]
    refine tsum_congr fun vc => ?_
    rw [probEvent_pure]
    by_cases hv : vc.1 = true
    · rw [if_pos ⟨hv, hfw⟩, mul_one]
      exact (if_pos hv).symm
    · rw [if_neg (fun h => hv h.1), mul_zero]
      exact (if_neg hv).symm
  · rw [if_neg hfw, zero_mul]
    refine ENNReal.tsum_eq_zero.mpr fun vc => ?_
    rw [probEvent_pure, if_neg (fun h => hfw h.2), mul_zero]

omit [SampleableType Chal] in
/-- **Support transfer.** On the support of the logged run, the extractor's scan-miss
indicator coincides with the cache-side pinning predicate (`CachePinned`), turning the
factored payoff into the log-free leaf `ksLeaf`. -/
private lemma EP_scanMiss_eq_EP_ksLeaf
    (prover : Stmt → M →
      OracleComp (unifSpec + fischlinROSpec Stmt Commit Chal Resp ρ b M)
        (FischlinProof Commit Chal Resp ρ))
    (x : Stmt) (msg : M) :
    EP (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅)
        (fun z =>
          (if fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none then 1 else 0) *
            Pr[= true | (simulateQ (fischlinImpl ρ b M)
              ((Fischlin (m := OracleComp (unifSpec
                  + fischlinROSpec Stmt Commit Chal Resp ρ b M))
                σ hr ρ b S M).verify x msg z.1.1)).run' z.2])
      = EP (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
            + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M))
          (prover x msg)).run).run ∅)
        (fun z => ksLeaf σ hr ρ b S M x msg z.1.1 z.2) := by
  classical
  rw [EP, EP]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ support (((simulateQ (idImplW (fischlinROSpec Stmt Commit Chal Resp ρ b M)
      + loggedROW (fischlinROSpec Stmt Commit Chal Resp ρ b M)) (prover x msg)).run).run ∅)
  · congr 1
    unfold ksLeaf
    have hiff := fischlinFindWitness_eq_none_iff_cachePinned σ ρ b M x z.1.1
      (log_subset_cache (prover x msg) hz) (cache_subset_log (prover x msg) hz)
    by_cases hfw : fischlinFindWitness σ ρ b M x z.1.1 z.1.2 = none
    · rw [if_pos hfw, if_pos (hiff.mp hfw)]
    · rw [if_neg hfw, if_neg fun hp => hfw (hiff.mpr hp)]
  · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]

omit [SampleableType Chal] in
/-- **Online-extraction reduction (Fischlin 2005, Theorem 2 core).** The Fischlin
knowledge-soundness bad event — the verifier accepts the cheating prover's proof yet the online
extractor recovers no
valid witness — occurs with probability at most `(Q+1)` (one slot per logged hash query, plus the
trivial slot) times the chance that a fresh tuple of `ρ` independent random-oracle answers lands in
the small-sum target set, namely `smallSumCount ρ b S / (2^b)^ρ`.

Argument sketch: special soundness with unique responses (`hss`, `hur`) implies that whenever the
extractor fails, every repetition's accepting transcript is pinned to a single logged query, so the
prover must have hit a small-sum assignment of `ρ` *fresh* uniform hash values without a second
accepting query at a different challenge. Union-bounding over the `≤ Q` logged queries and the
small-sum target set, and using independence of the `ρ` fresh answers, gives the denominator
`(2^b)^ρ`. -/
private lemma knowledgeSoundness_badEvent_le
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M) (Q : ℕ) (_hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q) (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ (↑(Q + 1) : ℝ≥0∞) * ↑(smallSumCount ρ b S) / ((↑(2 ^ b) : ℝ≥0∞) ^ ρ) := by
  classical
  letI : ∀ c, DecidablePred (ksDead σ ρ b M x msg c) := fun _ => Classical.decPred _
  -- Step 1: bound the bad event by the verifier-accepts-while-scan-misses event.
  refine le_trans (knowledgeSoundnessExp_bad_le_misses' σ hr ρ b S M hss adv.run x msg) ?_
  -- Step 2: factor the miss event through the logged prover run as an expected payoff.
  rw [ksSample_probEvent_eq_EP σ hr ρ b S M adv.run x msg,
    -- Step 3: on the support, swap the scan-miss indicator for the pinning predicate.
    EP_scanMiss_eq_EP_ksLeaf σ hr ρ b S M adv.run x msg,
    -- Step 4: drop the log, moving to the unlogged lazy-random-oracle run.
    dropLog_EP (adv.run x msg) ∅ (fun π cache => ksLeaf σ hr ρ b S M x msg π cache)]
  -- Step 5: run the supermartingale induction from the empty cache.
  refine le_trans (main_induction_gen_init ρ b S
    (ksRelevant σ ρ M x msg) (fun t => t.comList) (fun t => t.rep) (fun t => t.chal)
    (fun t₁ t₂ h₁ h₂ hk hi hc => ksRelevant_cell_inj σ ρ M hur x msg t₁ t₂ h₁ h₂ hk hi hc)
    (ksDead σ ρ b M x msg)
    (fun c t u k h => ksDead_mono σ ρ b M x msg c t u k h)
    (fun cache t t' u u' hrel hrel' hk hi hch hc' =>
      ksDead_kill σ ρ b M x msg cache t t' u u' hrel hrel' hk hi hch hc')
    (fun π cache => ksLeaf σ hr ρ b S M x msg π cache)
    (fun a cache keys st hINV => fischlin_leaf_le σ hr ρ b S M hur x msg a cache keys st hINV)
    (adv.run x msg) Q ((OracleComp.isQueryBoundP_congr_pred
      fun t => by cases t <;> exact Iff.rfl).mp (hQ x msg))) (le_of_eq ?_)
  -- Step 6: evaluate the fresh slot potential `μ = smallSumCount / (2^b)^ρ`.
  rw [slotPsi_none, ← mul_div_assoc, Nat.cast_pow, Nat.cast_ofNat]

omit [SampleableType Chal] in
/-- Knowledge soundness of the Fischlin transform via online (straight-line) extraction
(Fischlin 2005, Theorem 2).

If the Σ-protocol is specially sound with unique responses, then for any cheating prover
making at most `Q` hash queries, the probability that the verifier accepts but the
online extractor fails to recover a valid witness is at most
`(Q + 1) · (S + 1) · C(S + ρ - 1, ρ - 1) / 2^(bρ)`.

Unlike the Fiat-Shamir transform, this extraction is **straight-line** (no rewinding),
which enables a tight security reduction. -/
theorem knowledgeSoundness
    (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
    (adv : KnowledgeSoundnessAdv ρ b M)
    (Q : ℕ) (hρ : 0 < ρ)
    (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q)
    (x : Stmt) (msg : M) :
    Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
      ≤ knowledgeSoundnessError Q ρ b S := by
  refine le_trans (knowledgeSoundness_badEvent_le σ hr ρ b S M hss hur adv Q hρ hQ x msg) ?_
  rw [knowledgeSoundnessError]
  -- Monotonicity: replace the small-sum count by its stars-and-bars upper bound.
  gcongr
  exact_mod_cast smallSumCount_le ρ b S

/-! ### EUF-CMA Security

A tight EUF-CMA corollary for the Fischlin signature scheme requires an explicit
simulation of signing queries inside a hard-relation experiment. The previous
placeholder theorem overclaimed by bounding forgery probability solely by the
knowledge-soundness error, so we intentionally leave that corollary unstated
until the signing-simulation reduction is formalized. -/

end security

end Fischlin
