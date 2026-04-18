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

/-- A pointwise bound on the nonce sampler turns the bad-event probability into an explicit session
collision bound. -/
theorem unlinkBadExp_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)]).toReal ≤ maxNonceProb) :
    (Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary]).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  sorry

/-- Final unlinkability bound: two PRF advantages plus the explicit session-collision term. -/
theorem unlinkabilityAdvantage_le_two_prf_plus_sessionCollisionBound
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)]).toReal ≤ maxNonceProb) :
    ∃ multiAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      ∃ singleAdv : PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest,
        unlinkabilityAdvantage (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) prfs adversary ≤
            PRFScheme.prfAdvantage prfs.multiplePRFScheme multiAdv +
            PRFScheme.prfAdvantage prfs.singlePRFScheme singleAdv +
            ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  sorry

end Theorems

end PRFTagReader
