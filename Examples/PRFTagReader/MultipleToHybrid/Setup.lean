/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.Table

/-!
# PRF Tag/Reader Protocol — Instrumented multiple-session handler

Bad-flag instrumentation of the multiple-session ideal world of the unlinkability reduction.
Includes:

* the instrumented multiple-session handler `multipleBadQueryImpl` (joint state
  `MultipleBadState`) with its bad-flag advance `multipleBadAdvance` and per-query reductions
  (`multipleBadQueryImpl_tag_run`, `multipleBadQueryImpl_reader_run`);
* output equivalence with the uninstrumented handler
  (`probOutput_multipleBad_run'_eq_multipleIdeal`);
* monotonicity of the bad flag (`multipleBadQueryImpl_step_preserves_bad`,
  `multipleBadQueryImpl_run_preserves_bad`);
* structural `query_bind` reductions (`multipleBad_run'_query_bind'`,
  `multipleBad_run_query_bind'`).

This infrastructure is consumed by the eager-table handlers in the sibling
`MultipleToHybrid.EagerSetup` module and by the direct-coupling chain under `DirectCoupling/`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

section EagerComposed

/-! ### Multiple-to-hybrid: the instrumented multiple-session handler

`multipleIdealQueryImpl`'s state — a lazy random-oracle cache over `(TagId × Nonce)` — cannot
express "a within-tag tag–tag nonce collision has occurred": the cache key does not record whether
a cell was written by a tag draw or by a reader query, and a collision is history. The
instrumented handler `multipleBadQueryImpl` carries, beside the multiple-ideal state, a full
bad-world `UnlinkBadState` whose `bad` flag fires exactly on a tag-written cell collision. Its
*output bit* is identical to `multipleIdealQueryImpl`'s — the instrumentation only threads an extra
state component — so `Pr[= true]` is unchanged (`probOutput_multipleBad_run'_eq_multipleIdeal`).
The `bad` flag of `multipleBadAdvance` fires exactly when a tag query repeats a within-tag
`(tag, nonce)` pair (the `responses` cell for that pair is already populated), so its probability
records the within-tag nonce-collision mass. -/

/-- Joint handler state for the instrumented multiple-session world: the multiple-ideal state
(session counters + lazy random-oracle cache over `TagId × Nonce`) paired with a full bad-world
`UnlinkBadState` whose `responses` cache and `bad` flag detect within-tag nonce collisions. -/
abbrev MultipleBadState (TagId Nonce Digest : Type) (_sessionsPerTag : ℕ) : Type :=
  (UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ×
    UnlinkBadState TagId Nonce Digest

/-- Bad-world state advance on a tag query: given the previous bad state `sB` and the transcript
the multiple-ideal tag oracle produced, advance `sB` exactly as `unlinkBadTagQueryImpl` would —
recording the drawn digest and firing `bad` on a repeat `(tag, nonce)`. A `none` transcript (slot
exhausted) leaves `sB` untouched. -/
def multipleBadAdvance (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (r : Option (TagTranscript Nonce Digest)) : UnlinkBadState TagId Nonce Digest :=
  match r with
  | none => sB
  | some tr =>
      { sessionsUsed := Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1)
        responses := sB.responses.cacheQuery (tag, tr.nonce)
          (tr.auth :: Option.getD (sB.responses (tag, tr.nonce)) [])
        bad := sB.bad || (sB.responses (tag, tr.nonce)).isSome
        cacheBad := sB.cacheBad }

/-- `multipleIdealQueryImpl` re-targeted to the larger `MultipleBadState` monad: runs the
multiple-ideal handler on the inner state component and threads the extra `UnlinkBadState`
component through unchanged. This is the "base" handler that `multipleBadQueryImpl` instruments
via `QueryImpl.postInsert`.

Exists to bridge a framework gap: there is no standard `MonadLift` instance between
`StateT σ₁ m` and `StateT (σ₁ × σ₂) m`, so `postInsert` cannot lift a handler in the
smaller-state monad into the larger-state monad directly. The right fix is a general
`StateT.liftWith : MonadLift (StateT σ₁ m) (StateT (σ₁ × σ₂) m)` instance under
`VCVio/OracleComp/SimSemantics/StateT/`; until that lands, the manual lift here is the
template for future bad-flag-style instrumentation. -/
noncomputable def multipleIdealLiftedQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp) :=
  fun q => fun p =>
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q) p.1 >>= fun r =>
      pure (r.1, (r.2, p.2))

/-- Instrumented multiple-session handler: defined via `QueryImpl.postInsert` on top of
`multipleIdealLiftedQueryImpl`. The inserted side effect is a `modify` on the bad-world component
that fires `multipleBadAdvance` on a tag query and is a no-op on a reader query. The output bit and
inner-state evolution match `multipleIdealQueryImpl` exactly; only the extra `UnlinkBadState`
component carries the bad-flag instrumentation.

This shape validates the `postInsert` combinator for the "bad-flag" pattern: future reductions can
use the same idiom (lift the base ideal handler to the larger state, then `postInsert` a
`modify`-based bad-flag advance). -/
noncomputable def multipleBadQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp) :=
  (multipleIdealLiftedQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)).postInsert
    (fun q (r : (UnlinkOracleSpec TagId Nonce Digest).Range q) =>
      (modify (fun s : MultipleBadState TagId Nonce Digest sessionsPerTag =>
        match q, r with
        | Sum.inl tag, r => (s.1, multipleBadAdvance tag s.2 r)
        | Sum.inr _, _ => s) :
          StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp Unit))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleIdealLiftedQueryImpl` on a query: explicit form as an inner-state bind with the extra
state component preserved. -/
lemma multipleIdealLiftedQueryImpl_run
    (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleIdealLiftedQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) q) s.1 >>= fun r =>
        pure (r.1, (r.2, s.2)) := rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleBadQueryImpl` on a tag query: the multiple-ideal tag step with the bad-world component
advanced by `multipleBadAdvance`. -/
lemma multipleBadQueryImpl_tag_run (tag : TagId)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s.1 >>= fun r =>
        pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag s.2 r.1) := by
  change (multipleIdealLiftedQueryImpl (Sum.inl tag) s) >>= _ = _
  rw [multipleIdealLiftedQueryImpl_run, bind_assoc]
  refine bind_congr fun r => ?_; rw [pure_bind]; rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleBadQueryImpl` on a reader query: the multiple-ideal reader step, bad-world component
untouched. -/
lemma multipleBadQueryImpl_reader_run (transcript : TagTranscript Nonce Digest)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s.1 >>= fun r =>
        pure (r.1, (r.2.1, r.2.2), s.2) := by
  change (multipleIdealLiftedQueryImpl (Sum.inr transcript) s) >>= _ = _
  rw [multipleIdealLiftedQueryImpl_run, bind_assoc]
  refine bind_congr fun r => ?_; rw [pure_bind]; rfl

open OracleComp.ProgramLogic.Relational in
omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- **Multiple-to-hybrid, output equivalence.** The instrumented handler `multipleBadQueryImpl`
produces the same output distribution as `multipleIdealQueryImpl`: the bad-world component it
threads beside the multiple-ideal state never feeds back into the output bit. Hence `Pr[= true]` is
unchanged. -/
lemma probOutput_multipleBad_run'_eq_multipleIdeal
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' (s, sB)] =
      Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' s] := by
  have hrt : RelTriple
      ((simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) adversary).run' (s, sB))
      ((simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) adversary).run' s)
      (EqRel Bool) := by
    refine relTriple_simulateQ_run'
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag))
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag))
      (fun s₁ s₂ => s₁.1 = s₂) adversary ?_ (s, sB) s rfl
    intro t s₁ s₂ hs
    -- the head: `multipleBadQueryImpl t s₁` is `multipleIdealQueryImpl t s₁.1 >>= pure (…)`
    subst hs
    cases t with
    | inl tag =>
      change RelTriple ((multipleBadQueryImpl (Sum.inl tag)) s₁) _ _
      rw [multipleBadQueryImpl_tag_run]
      refine relTriple_of_evalDist_eq_right
        (congrArg evalDist (bind_pure ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s₁.1))) ?_
      refine relTriple_bind (relTriple_refl _) ?_
      rintro a b rfl
      exact relTriple_pure_pure ⟨rfl, rfl⟩
    | inr transcript =>
      change RelTriple ((multipleBadQueryImpl (Sum.inr transcript)) s₁) _ _
      rw [multipleBadQueryImpl_reader_run]
      refine relTriple_of_evalDist_eq_right
        (congrArg evalDist (bind_pure ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s₁.1))) ?_
      refine relTriple_bind (relTriple_refl _) ?_
      rintro a b rfl
      exact relTriple_pure_pure ⟨rfl, rfl⟩
  exact probOutput_eq_of_relTriple_eqRel hrt true

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The bad flag threaded by `multipleBadQueryImpl` is monotone under a single per-query step:
started from a `MultipleBadState` whose bad flag is set, every output state still has it set.
`multipleBadAdvance` only ever OR-s into the flag, and reader queries leave the bad-world component
untouched. -/
lemma multipleBadQueryImpl_step_preserves_bad
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) s), z.2.2.bad = true := by
  intro z hz
  cases t with
  | inl tag =>
    rw [multipleBadQueryImpl_tag_run tag s] at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz; subst hz
    cases r.1 <;> simp [multipleBadAdvance, hbad]
  | inr transcript =>
    rw [multipleBadQueryImpl_reader_run transcript s] at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz; subst hz; exact hbad

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Bad monotonicity for a full `simulateQ multipleBadQueryImpl` run: started from a state whose
bad flag is set, every reachable output state keeps it set. This is the `hmono` hypothesis of the
heterogeneous bad+slack `simulateQ` rule. -/
lemma multipleBadQueryImpl_run_preserves_bad {α : Type}
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run s), z.2.2.bad = true :=
  OracleComp.simulateQ_run_preservesInv
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag))
    (fun s : MultipleBadState TagId Nonce Digest sessionsPerTag => s.2.bad = true)
    (fun t s h z hz => multipleBadQueryImpl_step_preserves_bad t s h z hz) oa s hbad

end EagerComposed

/-! ### Structural `query_bind` reductions for the instrumented handler

The two lemmas below expose `simulateQ multipleBadQueryImpl` of a `query_bind` as a single
monadic `bind`: the per-query handler applied to the head, then the recursive `simulateQ` of the
continuation threaded through the resulting state. They are pure rewriting facts (`simulateQ` is
a monad morphism). -/

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadQueryImpl` of a `query_bind`, run from a state and projected to its
output bit: the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleBad_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' s =
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t s) >>= fun p =>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadQueryImpl` of a `query_bind`, run from a state and projected to its full
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleBad_run_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t s) >>= fun p =>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl


end UnlinkReduction

end PRFTagReader
