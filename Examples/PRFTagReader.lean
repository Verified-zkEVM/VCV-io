/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# PRF Tag/Reader Protocol

This file formalizes a simple RFID-style tag/reader protocol. Each tag is assigned a secret and,
when queried, samples a fresh nonce `n` and outputs `(n, F(secret, n))`. A reader accepts a
transcript `(n, a)` whenever some registered tag secret makes `a` equal to `F(secret, n)`.

The file defines:

- an active authentication game, where the adversary wins by making the reader accept a transcript
  that was not previously emitted by the honest tag oracle;
- a multiple-session unlinkability game, where all sessions of a tag reuse the same per-tag secret;
- a single-session unlinkability game, where each session uses an independent per-session secret;
- an intermediate bad-event world that records nonce collisions across repeated sessions.

The theorem statements at the end package the intended security story: authentication reduces to
PRF security plus an ideal-world argument, and unlinkability reduces to PRF security plus a nonce
collision bound.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

/-- Transcript emitted by a tag in one session: a fresh nonce together with its authenticator. -/
structure TagTranscript (Nonce Digest : Type) where
  nonce : Nonce
  auth : Digest
deriving DecidableEq, Repr

/-- Reader's protocol response. `ok` means that the transcript was accepted, and `ko` means that
it was rejected. -/
inductive ReaderReply where
  | ok
  | ko
deriving DecidableEq, Repr, Inhabited

namespace ReaderReply

/-- Convert a boolean acceptance decision into the concrete protocol reply. -/
def ofBool : Bool → ReaderReply
  | true => .ok
  | false => .ko

/-- Predicate exposing whether a reader reply is accepting. -/
def accepts : ReaderReply → Bool
  | .ok => true
  | .ko => false

end ReaderReply

/-- Session-slot assignment for a tag/reader world with `sessionsPerTag` many protocol sessions
available to each tag. Real unlinkability worlds reuse one slot per tag; ideal worlds may allocate
a fresh slot per session. -/
structure SessionPattern (TagId Slot : Type) (sessionsPerTag : ℕ) where
  slot : TagId → Fin sessionsPerTag → Slot

section Pattern

variable {TagId : Type} (sessionsPerTag : ℕ)

/-- Real session pattern: every session of a given tag reuses the same slot. -/
def multiplePattern : SessionPattern TagId TagId sessionsPerTag where
  slot := fun tag _ => tag

/-- Ideal unlinkability pattern: each session of each tag receives its own fresh slot. -/
def singlePattern : SessionPattern TagId (TagId × Fin sessionsPerTag) sessionsPerTag where
  slot := fun tag sid => (tag, sid)

end Pattern

/-- Packaging of the two keyed hash families used by the protocol. `evalMultiple` models secret
reuse across all sessions of a tag, while `evalSingle` models an independent secret for each
session of each tag. -/
structure TagReaderPRFs (K TagId Nonce Digest : Type) (sessionsPerTag : ℕ) where
  keygen : ProbComp K
  evalMultiple : K → TagId → Nonce → Digest
  evalSingle : K → TagId → Fin sessionsPerTag → Nonce → Digest

namespace TagReaderPRFs

variable {K TagId Nonce Digest : Type} {sessionsPerTag : ℕ}
  (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)

/-- Derived PRF scheme for the multiple-session world. -/
def multiplePRFScheme : PRFScheme K (TagId × Nonce) Digest where
  keygen := prfs.keygen
  eval := fun k input => prfs.evalMultiple k input.1 input.2

/-- Derived PRF scheme for the single-session world. -/
def singlePRFScheme : PRFScheme K ((TagId × Fin sessionsPerTag) × Nonce) Digest where
  keygen := prfs.keygen
  eval := fun k input => prfs.evalSingle k input.1.1 input.1.2 input.2

end TagReaderPRFs

/-- Authentication-game state: the honest tag transcripts emitted so far, together with all
reader acceptances that cannot be traced back to a prior honest tag output. -/
structure AuthState (TagId Nonce Digest : Type) where
  honestOutputs : Finset (TagId × TagTranscript Nonce Digest)
  readerForged : Finset (TagId × TagTranscript Nonce Digest)

/-- Ideal authentication-game state: the cached random-function table, together with the same
observable logs used in the real game. -/
structure AuthIdealState (TagId Nonce Digest : Type) where
  responses : ((TagId × Nonce) →ₒ Digest).QueryCache
  honestOutputs : Finset (TagId × TagTranscript Nonce Digest)
  readerForged : Finset (TagId × TagTranscript Nonce Digest)

section AuthState

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]

/-- Initial real authentication-game state. -/
def AuthState.init : AuthState TagId Nonce Digest where
  honestOutputs := ∅
  readerForged := ∅

/-- Initial ideal authentication-game state. -/
def AuthIdealState.init : AuthIdealState TagId Nonce Digest where
  responses := ∅
  honestOutputs := ∅
  readerForged := ∅

end AuthState

/-- Unlinkability-game state: how many sessions of each tag have already been consumed. -/
structure UnlinkState (TagId : Type) where
  sessionsUsed : TagId → ℕ

/-- Bad-world state for the multiple-session unlinkability proof: session counters, the list of
random-function responses seen for each `(tag, nonce)` pair, and the bad-event flag. -/
structure UnlinkBadState (TagId Nonce Digest : Type) where
  sessionsUsed : TagId → ℕ
  responses : ((TagId × Nonce) →ₒ List Digest).QueryCache
  bad : Bool

section UnlinkState

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]

/-- Initial unlinkability-game state. -/
def UnlinkState.init : UnlinkState TagId where
  sessionsUsed := fun _ => 0

/-- Initial unlinkability bad-event state. -/
def UnlinkBadState.init : UnlinkBadState TagId Nonce Digest where
  sessionsUsed := fun _ => 0
  responses := ∅
  bad := false

end UnlinkState

/-- Authentication-game oracle interface: a tag oracle and a reader oracle. -/
def AuthOracleSpec (TagId Nonce Digest : Type) :=
  (TagId →ₒ TagTranscript Nonce Digest) + ((TagTranscript Nonce Digest) →ₒ ReaderReply)

/-- Unlinkability-game oracle interface: a session-bounded tag oracle and a reader oracle. -/
def UnlinkOracleSpec (TagId Nonce Digest : Type) :=
  (TagId →ₒ Option (TagTranscript Nonce Digest)) +
    ((TagTranscript Nonce Digest) →ₒ ReaderReply)

/-- Authentication adversaries are oracle computations over the tag and reader interfaces. -/
abbrev AuthAdversary (TagId Nonce Digest : Type) :=
  OracleComp (AuthOracleSpec TagId Nonce Digest) Unit

/-- Unlinkability adversaries are oracle computations over the bounded-tag and reader interfaces. -/
abbrev UnlinkAdversary (TagId Nonce Digest : Type) :=
  OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool

section AuthGame

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]

/-- Honest tag oracle for the real authentication game. -/
def authTagQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthState TagId Nonce Digest) ProbComp) := fun tag => do
        let st ← get
        let nonce ← ($ᵗ Nonce : ProbComp Nonce)
        let auth := hash tag nonce
        let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
        set
          { st with
            honestOutputs := insert (tag, transcript) st.honestOutputs }
        return transcript

/-- Reader oracle for the real authentication game. It accepts any transcript that
matches some tag's hash image and logs acceptances that were never emitted by the honest tag
oracle. -/
def authReaderQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthState TagId Nonce Digest) ProbComp) := fun transcript => do
        let st ← get
        let accepted := decide (∃ tag, hash tag transcript.nonce = transcript.auth)
        let newForged := Finset.univ.filter fun tag =>
          hash tag transcript.nonce = transcript.auth ∧ (tag, transcript) ∉ st.honestOutputs
        set { st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) }
        return ReaderReply.ofBool accepted

/-- Combined real-game oracle implementation for authentication. -/
def authRealQueryImpl (hash : TagId → Nonce → Digest) :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthState TagId Nonce Digest) ProbComp) :=
  authTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hash +
    authReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) hash

/-- Real active-authentication experiment. -/
def authExp {K : Type} {sessionsPerTag : ℕ}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  let (_, st) ← (simulateQ
    (authRealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (fun tag nonce => prfs.evalMultiple k tag nonce))
    adversary).run AuthState.init
  return decide (st.readerForged ≠ ∅)

end AuthGame

section AuthIdealGame

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]

/-- Honest tag oracle for the ideal authentication world. It queries a lazy random
function table and records the emitted transcript. -/
def authIdealTagQueryImpl :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun tag => do
        let st ← get
        let nonce ← ($ᵗ Nonce : ProbComp Nonce)
        let key := (tag, nonce)
        let (auth, responses) ←
          match st.responses key with
          | some out => pure (out, st.responses)
          | none => do
              let out ← ($ᵗ Digest : ProbComp Digest)
              pure (out, st.responses.cacheQuery key out)
        let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
        set
          ({ responses := responses
             honestOutputs := insert (tag, transcript) st.honestOutputs
             readerForged := st.readerForged } : AuthIdealState TagId Nonce Digest)
        return transcript

/-- Reader oracle for the ideal authentication world. It only accepts transcripts that
were previously generated for the queried tag and nonce in the cached random-function table. -/
def authIdealReaderQueryImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) := fun transcript => do
        let st ← get
        let matching := Finset.univ.filter fun tag =>
          st.responses (tag, transcript.nonce) = some transcript.auth
        let newForged := matching.filter fun tag =>
          (tag, transcript) ∉ st.honestOutputs
        set
          ({ responses := st.responses
             honestOutputs := st.honestOutputs
             readerForged := st.readerForged ∪ (newForged.image (·, transcript))
           } : AuthIdealState TagId Nonce Digest)
        return ReaderReply.ofBool (decide (matching.Nonempty))

/-- Combined ideal-game oracle implementation for authentication. -/
def authIdealQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthIdealState TagId Nonce Digest) ProbComp) :=
  authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authIdealReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- Ideal active-authentication experiment. The keyed hash is replaced by a lazy random function on
`(tag, nonce)`, and the reader only accepts transcripts that match the cached table. -/
def authIdealExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
    adversary).run AuthIdealState.init
  return decide (st.readerForged ≠ ∅)

end AuthIdealGame

section UnlinkGame

variable {TagId Slot Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Reader acceptance for a fixed tag in a given unlinkability session pattern. -/
def tagAccepts (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag)
    (tag : TagId) (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ sid : Fin sessionsPerTag,
    hash (pattern.slot tag sid) transcript.nonce = transcript.auth)

/-- Reader acceptance test for a fixed unlinkability session pattern. -/
def unlinkReaderAccepts (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag,
    tagAccepts (TagId := TagId) (Slot := Slot) (Nonce := Nonce) (Digest := Digest)
      hash pattern tag transcript)

/-- Tag oracle for a fixed unlinkability session pattern. It returns `none` once the session cap
for the queried tag is exhausted. -/
def unlinkTagQueryImpl (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag) :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkState TagId) ProbComp) := fun tag => do
        let st ← get
        if h : st.sessionsUsed tag < sessionsPerTag then
          let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          let auth := hash (pattern.slot tag sid) nonce
          let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
          set
            { st with
              sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
          return some transcript
        else
          return none

/-- Reader oracle for a fixed unlinkability session pattern. -/
def unlinkReaderQueryImpl (hash : Slot → Nonce → Digest)
    (pattern : SessionPattern TagId Slot sessionsPerTag) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkState TagId) ProbComp) := fun transcript =>
        return ReaderReply.ofBool <| unlinkReaderAccepts (TagId := TagId) (Slot := Slot)
          (Nonce := Nonce) (Digest := Digest) hash pattern transcript

/-- Combined multiple-session unlinkability oracle implementation. -/
def unlinkMultipleQueryImpl {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (k : K) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
    (fun tag nonce => prfs.evalMultiple k tag nonce)
    (multiplePattern (TagId := TagId) sessionsPerTag) +
    unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
      (fun tag nonce => prfs.evalMultiple k tag nonce)
      (multiplePattern (TagId := TagId) sessionsPerTag)

/-- Combined single-session unlinkability oracle implementation. -/
def unlinkSingleQueryImpl {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (k : K) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId) ProbComp) :=
  unlinkTagQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
    (Nonce := Nonce) (Digest := Digest)
    (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
    (singlePattern (TagId := TagId) sessionsPerTag) +
    unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag)
      (Nonce := Nonce) (Digest := Digest)
      (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
      (singlePattern (TagId := TagId) sessionsPerTag)

/-- Multiple-session unlinkability world: each tag reuses its own slot across all sessions. -/
def unlinkMultipleExp {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  (simulateQ (unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) prfs k) adversary).run' UnlinkState.init

/-- Single-session unlinkability world: each tag query consumes a fresh slot, while the reader
checks all session slots for that tag. -/
def unlinkSingleExp {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let k ← prfs.keygen
  (simulateQ (unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) prfs k) adversary).run' UnlinkState.init

/-- One-sided unlinkability gap `Pr[Multiple] - Pr[Single]` between the two session-allocation
worlds. -/
noncomputable def unlinkabilityAdvantage {K : Type}
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) : ℝ :=
  (Pr[= true | unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal -
    (Pr[= true | unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary]).toReal

end UnlinkGame

section BadEvent

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Tag oracle for the `RF_bad` multiple-session collision world. It
samples a fresh ideal hash output on every tag query, records all outputs associated with a given
`(tag, nonce)` pair, and sets `bad` once some pair is queried twice. -/
def unlinkBadTagQueryImpl :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) := fun tag => do
        let st ← get
        if _h : st.sessionsUsed tag < sessionsPerTag then
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          let auth ← ($ᵗ Digest : ProbComp Digest)
          let outputs := auth :: Option.getD (st.responses (tag, nonce)) []
          let bad := st.bad || (st.responses (tag, nonce)).isSome
          let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
          set
            ({ sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
               responses := st.responses.cacheQuery (tag, nonce) outputs
               bad := bad } : UnlinkBadState TagId Nonce Digest)
          return some transcript
        else
          return none

/-- Reader oracle for the `RF_bad` multiple-session world. It accepts when the queried digest
appears among the cached random-function outputs for some tag at the given nonce. -/
def unlinkBadReaderQueryImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) := fun transcript => do
        let st ← get
        let accepted := decide (∃ tag ∈ (Finset.univ : Finset TagId),
          transcript.auth ∈ ((st.responses (tag, transcript.nonce)).getD []))
        return ReaderReply.ofBool accepted

/-- Oracle implementation for the `RF_bad` multiple-session world. -/
def unlinkBadQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkBadState TagId Nonce Digest) ProbComp) :=
  unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag)
    +
    unlinkBadReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- Bad-event experiment from the `RF_bad` multiple-session collision world. -/
def unlinkBadExp
    (adversary : UnlinkAdversary TagId Nonce Digest) : ProbComp Bool := do
  let (_, st) ← (simulateQ
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag))
    adversary).run UnlinkBadState.init
  return st.bad

end BadEvent

section Theorems

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Authentication reduction statement: the real game is bounded by a PRF distinguishing advantage
plus the success probability in the ideal authentication world. -/
theorem authExp_le_prfAdvantage_add_authIdeal
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    ∃ prfAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      (Pr[= true | authExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) prfs adversary]).toReal ≤
        PRFScheme.prfAdvantage prfs.multiplePRFScheme prfAdv +
        (Pr[= true | authIdealExp (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) adversary]).toReal := by
  sorry

omit [Nonempty TagId] in
/-- In the ideal authentication world, a forged reader acceptance never occurs. -/
theorem authIdealExp_eq_zero
    (adversary : AuthAdversary TagId Nonce Digest) :
    Pr[= true | authIdealExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) adversary] = 0 := by
  let ForgedInv : AuthIdealState TagId Nonce Digest → Prop := fun st => st.readerForged = ∅
  let CacheInv : AuthIdealState TagId Nonce Digest → Prop := fun st =>
    ∀ tag nonce auth, st.responses (tag, nonce) = some auth →
      (tag, ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest)) ∈ st.honestOutputs
  have htagForged :
      QueryImpl.PreservesInv
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        ForgedInv := by
    intro tag st hst z hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion] at hz
    rcases hz with ⟨i, hz⟩
    cases hresp : st.responses (tag, i) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ, Set.mem_range] at hz
      grind
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      grind
  have htagCached :
      QueryImpl.PreservesInv
        (authIdealTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        CacheInv := by
    intro tag st hst z hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion] at hz
    rcases hz with ⟨nonce, hz⟩
    cases hresp : st.responses (tag, nonce) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ, Set.mem_range] at hz
      rcases hz with ⟨auth, rfl⟩
      intro tag' nonce' auth' hlookup
      by_cases hkey : (tag', nonce') = (tag, nonce)
      · cases hkey
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hlookup
        subst auth'
        simp
      · have hlookup' : st.responses (tag', nonce') = some auth' := by
          simpa [QueryCache.cacheQuery_of_ne (cache := st.responses) auth hkey] using hlookup
        exact Finset.mem_insert_of_mem (hst tag' nonce' auth' hlookup')
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      rcases hz with rfl
      intro tag' nonce' auth' hlookup
      exact Finset.mem_insert_of_mem (hst tag' nonce' auth' hlookup)
  have hreaderForged :
      ∀ transcript st, ForgedInv st ∧ CacheInv st →
        ∀ z ∈
            support
              (((authIdealReaderQueryImpl
                  (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) transcript).run st),
          ForgedInv z.2 := by
    intro transcript st hst z hz
    have hz' := hz
    have hcached := hst.2
    unfold authIdealReaderQueryImpl at hz'
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
      map_pure, support_pure, Set.mem_singleton_iff] at hz'
    rcases hz' with rfl
    unfold ForgedInv at *
    have hnewForged :
        ((Finset.univ.filter fun tag =>
          st.responses (tag, transcript.nonce) = some transcript.auth).filter fun tag =>
            (tag, transcript) ∉ st.honestOutputs) = ∅ := by
      ext tag
      constructor
      · intro hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨hmatch, hnotmem⟩
        simpa using (False.elim (hnotmem (hcached tag transcript.nonce transcript.auth hmatch)))
      · intro hmem
        simp at hmem
    rw [hst.1, hnewForged, Finset.image_empty, Finset.empty_union]
  have hreaderCached :
      QueryImpl.PreservesInv
        (authIdealReaderQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        CacheInv := by
    intro transcript st hst z hz
    unfold authIdealReaderQueryImpl at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
      map_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  have himpl :
      QueryImpl.PreservesInv
        (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (fun st => ForgedInv st ∧ CacheInv st) := by
    intro t st hst z hz
    cases t with
    | inl tag =>
        exact (QueryImpl.PreservesInv.and htagForged htagCached) tag st hst z hz
    | inr transcript =>
        exact ⟨hreaderForged transcript st hst z hz, hreaderCached transcript st hst.2 z hz⟩
  have hfinal :
      ∀ z ∈
          support
            ((simulateQ
                (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
                adversary).run AuthIdealState.init),
        z.2.readerForged = ∅ := by
    intro z hz
    have hz' :=
      OracleComp.simulateQ_run_preservesInv
        (authIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest))
        (fun st => ForgedInv st ∧ CacheInv st) himpl adversary AuthIdealState.init
        (by simp [ForgedInv, CacheInv, AuthIdealState.init]) z hz
    grind
  refine (probOutput_eq_zero_iff
    (mx := authIdealExp (TagId := TagId) (Nonce := Nonce) (Digest := Digest) adversary)
    (x := true)).mpr ?_
  intro hmem
  rw [authIdealExp, mem_support_bind_iff] at hmem
  grind

/-- Unlinkability reduction statement: the multiple-vs-single gap is bounded by one PRF advantage
for the multiple-session world, one PRF advantage for the single-session world, and the bad-event
probability from the intermediate collision world. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_collision
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal := by
  sorry

/-- The number of still-available successful tag sessions in a bad-event state. -/
private def unlinkBadRemaining (st : UnlinkBadState TagId Nonce Digest) : ℕ :=
  (Finset.univ : Finset TagId).sum fun tag => sessionsPerTag - st.sessionsUsed tag

/-- Reachable bad-event states only cache nonces that came from successful tag sessions. For each
tag, we retain a finite witness set of cached nonces whose size is bounded by that tag's session
counter. -/
private def unlinkBadCacheBounded (st : UnlinkBadState TagId Nonce Digest) : Prop :=
  ∀ tag : TagId, ∃ nonces : Finset Nonce,
    nonces.card ≤ st.sessionsUsed tag ∧
      ∀ nonce : Nonce, (st.responses (tag, nonce)).isSome = true → nonce ∈ nonces

/-- State produced by a successful `RF_bad` tag query after sampling `nonce` and `auth`. -/
private def unlinkBadTagNext
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest) : UnlinkBadState TagId Nonce Digest :=
  { sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
    responses := st.responses.cacheQuery (tag, nonce)
      (auth :: Option.getD (st.responses (tag, nonce)) [])
    bad := st.bad || (st.responses (tag, nonce)).isSome }

omit [Fintype TagId] [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial state satisfies `unlinkBadCacheBounded`: the response cache is empty, so the empty
witness set trivially bounds each tag's nonce count. -/
private lemma unlinkBadCacheBounded_init :
    unlinkBadCacheBounded
      (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) := by
  intro tag
  refine ⟨∅, by simp [UnlinkBadState.init], ?_⟩
  intro nonce hcached
  simp [UnlinkBadState.init] at hcached

omit [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The `unlinkBadReaderQueryImpl` does not modify the state. -/
private lemma unlinkBadReaderQueryImpl_state_eq
    (transcript : TagTranscript Nonce Digest)
    (st : UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((unlinkBadReaderQueryImpl (TagId := TagId)
        (Nonce := Nonce) (Digest := Digest) transcript).run st),
      z.2 = st := by
  intro z hz
  unfold unlinkBadReaderQueryImpl at hz
  simpa using congrArg Prod.snd hz

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- When the tag still has a free slot (`sessionsUsed tag < sessionsPerTag`), the tag oracle samples
a fresh nonce and digest and advances the state via `unlinkBadTagNext`. -/
private lemma unlinkBadTagQueryImpl_run_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run st =
      (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
          pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
            unlinkBadTagNext tag st nonce auth)) := by
  simp [unlinkBadTagQueryImpl, unlinkBadTagNext, hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- When the tag has exhausted its slot budget, the tag oracle returns `none` and leaves the state
unchanged. -/
private lemma unlinkBadTagQueryImpl_run_of_not_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run st = pure (none, st) := by
  simp [unlinkBadTagQueryImpl, hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Every outcome in the support of a successful tag query has the form
`(some ⟨nonce, auth⟩, unlinkBadTagNext tag st nonce auth)` for some sampled `nonce` and `auth`. -/
private lemma unlinkBadTagQueryImpl_support_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    ∀ z ∈ support ((unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) tag).run st),
      ∃ nonce auth,
        z = (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
          unlinkBadTagNext tag st nonce auth) := by
  intro z hz
  rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
    mem_support_bind_iff] at hz
  rcases hz with ⟨nonce, _, hz⟩
  rw [mem_support_bind_iff] at hz
  rcases hz with ⟨auth, _, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  exact ⟨nonce, auth, hz⟩

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
    [DecidableEq Digest] [SampleableType Digest] in
/-- `unlinkBadCacheBounded` is preserved by a successful tag step: the new nonce is added to the
witness set, keeping its cardinality within the incremented session counter. -/
private lemma unlinkBadTagNext_cacheBounded
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hbounded : unlinkBadCacheBounded st) :
    unlinkBadCacheBounded (unlinkBadTagNext tag st nonce auth) := by
  intro tag'
  obtain ⟨S, hScard, hS⟩ := hbounded tag'
  by_cases htag : tag' = tag
  · subst tag'
    refine ⟨insert nonce S, ?_, ?_⟩
    · have hcard : (insert nonce S).card ≤ st.sessionsUsed tag + 1 :=
        (Finset.card_insert_le nonce S).trans (by omega)
      simpa [unlinkBadTagNext] using hcard
    · intro nonce' hcached
      by_cases hkey : (tag, nonce') = (tag, nonce)
      · simp only [Prod.mk.injEq, true_and] at hkey
        subst nonce'
        exact Finset.mem_insert_self nonce S
      · have hsome : (st.responses (tag, nonce')).isSome = true := by
          simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached
        exact Finset.mem_insert_of_mem (hS nonce' hsome)
  · refine ⟨S, ?_, ?_⟩
    · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hScard
    · intro nonce' hcached
      have hkey : (tag', nonce') ≠ (tag, nonce) := by
        intro h
        exact htag (Prod.ext_iff.mp h).1
      have hsome : (st.responses (tag', nonce')).isSome = true := by
        simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached
      exact hS nonce' hsome

omit [Fintype TagId] [Nonempty TagId]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A successful tag step does not push any tag's session counter above `sessionsPerTag`,
preserving the `sessionsUsed ≤ sessionsPerTag` invariant needed by the induction. -/
private lemma unlinkBadTagNext_sessionsUsed_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    ∀ tag', (unlinkBadTagNext tag st nonce auth).sessionsUsed tag' ≤ sessionsPerTag := by
  intro tag'
  by_cases htag : tag' = tag
  · subst htag
    simp [unlinkBadTagNext, Function.update_self]
    omega
  · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hused tag'

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
    [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A successful tag step decrements `unlinkBadRemaining` by exactly 1, which is the key
step in the union-bound induction. -/
private lemma unlinkBadRemaining_tagNext
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth) =
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
  let remainingAt : TagId → ℕ := fun tag' => sessionsPerTag - st.sessionsUsed tag'
  have hpos : 0 < remainingAt tag := Nat.sub_pos_of_lt hslot
  have hpoint :
      (fun tag' : TagId =>
        sessionsPerTag -
          (unlinkBadTagNext tag st nonce auth).sessionsUsed tag') =
        Function.update remainingAt tag (remainingAt tag - 1) := by
    funext tag'
    by_cases htag : tag' = tag
    · subst htag
      simp [unlinkBadTagNext, remainingAt, Function.update_self]
      omega
    · simp [unlinkBadTagNext, remainingAt, Function.update_of_ne htag]
  calc
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth)
        = ∑ tag' : TagId, Function.update remainingAt tag (remainingAt tag - 1) tag' := by
          simp [unlinkBadRemaining, hpoint]
    _ = (∑ tag' : TagId, remainingAt tag') - 1 := sum_update_pred hpos
    _ = unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
          simp [unlinkBadRemaining, remainingAt]

omit [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]
    [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- If any tag still has a free slot, the total remaining budget is positive. Used to justify
the `- 1` arithmetic in `unlinkBadRemaining_tagNext`. -/
private lemma unlinkBadRemaining_pos_of_slot
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    0 < unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st := by
  have hterm : 0 < sessionsPerTag - st.sessionsUsed tag := Nat.sub_pos_of_lt hslot
  have hle : sessionsPerTag - st.sessionsUsed tag ≤
      (Finset.univ : Finset TagId).sum
        (fun tag' => sessionsPerTag - st.sessionsUsed tag') :=
    Finset.single_le_sum (s := (Finset.univ : Finset TagId))
      (f := fun tag' => sessionsPerTag - st.sessionsUsed tag')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ tag)
  exact lt_of_lt_of_le hterm (by simpa [unlinkBadRemaining] using hle)

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- A single tag step raises `bad` with probability at most `sessionsUsed tag * maxNonceProb`:
the new nonce collides with one of the (at most `sessionsUsed tag`) previously cached nonces,
each matchable with probability at most `maxNonceProb`. -/
private lemma unlinkBadTagStep_bad_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (hbad : st.bad = false)
    (hbounded : unlinkBadCacheBounded st) :
    Pr[fun z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest =>
        z.2.bad = true |
      (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) tag).run st] ≤
      (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
  by_cases hslot : st.sessionsUsed tag < sessionsPerTag
  · rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
      probEvent_bind_eq_tsum]
    have hinner : ∀ nonce : Nonce,
        Pr[fun z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest =>
            z.2.bad = true |
          ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
            pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
              unlinkBadTagNext tag st nonce auth)] =
          if (st.responses (tag, nonce)).isSome then 1 else 0 := by
      intro nonce
      by_cases hcached : (st.responses (tag, nonce)).isSome = true
      · simp [unlinkBadTagNext, hbad, hcached]
      · simp [unlinkBadTagNext, hbad, hcached]
    simp_rw [hinner]
    obtain ⟨S, hScard, hS⟩ := hbounded tag
    calc
      ∑' nonce : Nonce,
          Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (st.responses (tag, nonce)).isSome then 1 else 0)
          = Pr[fun nonce : Nonce => (st.responses (tag, nonce)).isSome = true |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            simp only [probEvent_eq_tsum_ite]
            refine tsum_congr fun nonce => ?_
            by_cases hcached : (st.responses (tag, nonce)).isSome = true
            · simp [hcached]
            · simp [hcached]
      _ ≤ Pr[fun nonce : Nonce => ∃ n ∈ S, nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            apply probEvent_mono
            intro nonce _ hcached
            exact ⟨nonce, hS nonce hcached, rfl⟩
      _ ≤ ∑ n ∈ S, Pr[fun nonce : Nonce => nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] :=
            probEvent_exists_finset_le_sum S ($ᵗ Nonce : ProbComp Nonce)
              (fun n nonce => nonce = n)
      _ ≤ ∑ _n ∈ S, maxNonceProb := by
            apply Finset.sum_le_sum
            intro n hn
            simpa [probEvent_eq_eq_probOutput] using hmax n
      _ = (S.card : ℝ≥0∞) * maxNonceProb := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
            exact mul_le_mul' (Nat.cast_le.mpr hScard) le_rfl
  · rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
    simp [hbad]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- For any adversary and state `st` with `bad = false`,
the probability that bad fires is at most
`(∑ tag, sessionsPerTag − st.sessionsUsed tag) * sessionsPerTag * maxNonceProb`. -/
private lemma simulateQ_unlinkBad_prob_le
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (st : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded st)
    (hbad : st.bad = false)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run st] ≤
      (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
  induction adversary using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hbad, Bool.false_eq_true,
      ite_false]
    exact zero_le _
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
    cases t with
    | inl tag =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inl]
      by_cases hslot : st.sessionsUsed tag < sessionsPerTag
      · let step :=
          (unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) tag).run st
        let cont := fun z : Option (TagTranscript Nonce Digest) ×
            UnlinkBadState TagId Nonce Digest =>
          (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) (oa z.1)).run z.2
        have hstep :
            Pr[fun z : Option (TagTranscript Nonce Digest) ×
                  UnlinkBadState TagId Nonce Digest => ¬ z.2.bad = false | step] ≤
              (sessionsPerTag : ℝ≥0∞) * maxNonceProb := by
          have hbadStep :=
            unlinkBadTagStep_bad_le (sessionsPerTag := sessionsPerTag)
              tag st maxNonceProb hmax hbad hbounded
          have hused_le :
              (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb ≤
                (sessionsPerTag : ℝ≥0∞) * maxNonceProb :=
            mul_le_mul' (Nat.cast_le.mpr (hused tag)) le_rfl
          simpa [step] using hbadStep.trans hused_le
        have hRpos := unlinkBadRemaining_pos_of_slot
          (sessionsPerTag := sessionsPerTag) tag st hslot
        have hcont :
            ∀ z ∈ support step, z.2.bad = false →
              Pr[fun y : Bool × UnlinkBadState TagId Nonce Digest => ¬ y.2.bad = false |
                  cont z] ≤
                ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) : ℝ≥0∞) *
                  ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
          intro z hz hzbad
          obtain ⟨nonce, auth, rfl⟩ :=
            unlinkBadTagQueryImpl_support_of_lt (sessionsPerTag := sessionsPerTag)
              tag st hslot z (by simpa [step] using hz)
          have hnextBounded :=
            unlinkBadTagNext_cacheBounded tag st nonce auth hbounded
          have hnextUsed :=
            unlinkBadTagNext_sessionsUsed_le (sessionsPerTag := sessionsPerTag)
              tag st nonce auth hslot hused
          have hnextRemaining :=
            unlinkBadRemaining_tagNext (sessionsPerTag := sessionsPerTag)
              tag st nonce auth hslot
          have hih :=
            ih (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest))
              (unlinkBadTagNext tag st nonce auth)
              hnextBounded hzbad hnextUsed
          simpa [cont, hnextRemaining] using hih
        have hcombine := probEvent_bind_le_add (mx := step) (my := cont)
          (p := fun z : Option (TagTranscript Nonce Digest) ×
            UnlinkBadState TagId Nonce Digest => z.2.bad = false)
          (q := fun y : Bool × UnlinkBadState TagId Nonce Digest => y.2.bad = false)
          (ε₁ := (sessionsPerTag : ℝ≥0∞) * maxNonceProb)
          (ε₂ := ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) :
              ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb))
          hstep hcont
        calc
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
              step >>= cont]
              ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb +
                  ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) :
                    ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                simpa [step, cont] using hcombine
          _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                let R := unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st
                let c := (sessionsPerTag : ℝ≥0∞) * maxNonceProb
                have hR : 1 + (R - 1) = R := Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hRpos)
                have hRcast : (1 : ℝ≥0∞) + ((R - 1 : ℕ) : ℝ≥0∞) = (R : ℝ≥0∞) := by
                  exact_mod_cast hR
                change c + ((R - 1 : ℕ) : ℝ≥0∞) * c = (R : ℝ≥0∞) * c
                nth_rw 1 [← one_mul c]
                rw [← add_mul, hRcast]
      · change
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            ((unlinkBadTagQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) tag).run st >>= fun p =>
              (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) (oa p.1)).run
                p.2)] ≤
            (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)
        rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
        simpa using ih none st hbounded hbad hused
    | inr transcript =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inr]
      rw [probEvent_bind_eq_tsum]
      calc ∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st] *
              Pr[fun w => w.2.bad | (simulateQ unlinkBadQueryImpl (oa z.1)).run z.2]
          ≤ ∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st] *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            apply ENNReal.tsum_le_tsum
            intro z
            by_cases hmem :
                z ∈ support ((unlinkBadReaderQueryImpl
                    (TagId := TagId) (Nonce := Nonce) (Digest := Digest) transcript).run st)
            · rw [unlinkBadReaderQueryImpl_state_eq transcript st z hmem]
              exact mul_le_mul' le_rfl (ih z.1 st hbounded hbad hused)
            · rw [probOutput_eq_zero_of_not_mem_support hmem]
              simp
        _ = (∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st]) *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            rw [ENNReal.tsum_mul_right]
        _ ≤ 1 * ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            gcongr
            exact tsum_probOutput_le_one
        _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := one_mul _

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- A pointwise bound on the nonce sampler turns the bad-event probability into an explicit session
collision bound. -/
theorem unlinkBadExp_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  have hmax_ENNReal : ∀ n : Nonce,
      Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ ENNReal.ofReal maxNonceProb := by
    intro n
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax n)
  have hlhs : Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init] := by
    rw [← probEvent_eq_eq_probOutput, unlinkBadExp, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    simp
  rw [hlhs]
  have hcore := simulateQ_unlinkBad_prob_le (sessionsPerTag := sessionsPerTag)
    adversary (ENNReal.ofReal maxNonceProb)
    hmax_ENNReal UnlinkBadState.init unlinkBadCacheBounded_init (by simp [UnlinkBadState.init])
    (by simp [UnlinkBadState.init])
  have hconv : (Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init]).toReal ≤
      ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
          (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) :
            ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * ENNReal.ofReal maxNonceProb)).toReal := by
    exact ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  have hremaining :
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) =
          sessionsPerTag * Fintype.card TagId := by
    simp [unlinkBadRemaining, UnlinkBadState.init, Finset.sum_const, Finset.card_univ,
      mul_comm]
  have hsupp : (support ($ᵗ Nonce : ProbComp Nonce)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]
    simp
  obtain ⟨nonce0, _⟩ := hsupp
  have hmax_nonneg : 0 ≤ maxNonceProb := ENNReal.toReal_nonneg.trans (hmax nonce0)
  simp only [
    hremaining, Nat.cast_mul, toReal_mul, toReal_natCast, ENNReal.toReal_ofReal hmax_nonneg
  ] at hconv
  grind

/-- Final unlinkability bound: two PRF advantages plus the explicit session-collision term. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  obtain ⟨multiAdv, singleAdv, hSum⟩ :=
    unlinkabilityAdvantage_le_two_prf_plus_collision prfs adversary
  refine ⟨multiAdv, singleAdv, hSum.trans ?_⟩
  have hBad := unlinkBadExp_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag)
    adversary maxNonceProb hmax
  linarith

end Theorems

end PRFTagReader
