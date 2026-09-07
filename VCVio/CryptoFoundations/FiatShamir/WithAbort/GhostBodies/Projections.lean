/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.GhostLayer

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: Projections

Projections of the ghost-instrumented run onto both hybrid games
(`ghostHybridImpl_proj_prog`, `ghostHybridImpl_proj_trans`), ghost-value
independence of the ghost-blind step, and the ghost-domain invariant
`ghostHybridImpl_preserves_signed_inv`.

Part of the hybrid signing-body development for the CMA-to-NMA reduction;
`VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Bodies` opens the
chain and holds the overview docstring.
-/

public section

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)
variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))

/-! ## Projections of the ghost-instrumented run

The ghost-instrumented run projects onto the Prog hybrid by overlaying the ghost layer
onto the real one, and onto the Trans hybrid by forgetting the ghost layer. Both are
per-step state projections in the sense of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`. -/

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma onCache_run {α : Type}
    (action : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp α)
    (s : (M × Commit →ₒ Chal).QueryCache × List M) :
    (onCache M action).run s = (fun ac : α × (M × Commit →ₒ Chal).QueryCache =>
      (ac.1, (ac.2, s.2))) <$> action.run s.1 := rfl

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma hybridSignImpl_run
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (msg : M) (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (hybridSignImpl M signBody msg).run (c, l) =
      (fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
        (ac.1, (ac.2, msg :: l))) <$> (signBody msg).run c := rfl

omit [SampleableType Stmt] in
lemma roStep_of_some {re : (M × Commit →ₒ Chal).QueryCache} {mc : M × Commit} {v : Chal}
    (h : re mc = some v) : roStep M re mc = pure (v, re) := by
  unfold roStep
  rw [h]

omit [SampleableType Stmt] in
lemma roStep_of_none {re : (M × Commit →ₒ Chal).QueryCache} {mc : M × Commit}
    (h : re mc = none) :
    roStep M re mc = uniformSample Chal >>= fun c => pure (c, re.cacheQuery mc c) := by
  unfold roStep
  rw [h]

omit [SampleableType Stmt] in
lemma hybridBaseImpl_run_ro (mc : M × Commit)
    (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (hybridBaseImpl (Commit := Commit) (Chal := Chal) M (.inr mc)).run (c, l) =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (cu.2, l))) <$> roStep M c mc := by
  have h : (onCache M ((unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))) (.inr mc))).run (c, l) =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (cu.2, l))) <$> roStep M c mc := by
    rw [QueryImpl.add_apply_inr, onCache_run]
    exact congrArg (fun x => (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
      (cu.1, (cu.2, l))) <$> x) (randomOracle_run_eq_roStep M c mc)
  exact h

omit [SampleableType Stmt] in
lemma ghostHybridImpl_run_ro_ghost_some (progSide : Bool) (pk : Stmt) (sk : Wit)
    {mc : M × Commit} {s : GhostState M Commit Chal} {v : Chal}
    (h : s.1.1.2 mc = some v) :
    (ghostHybridImpl ids M maxAttempts progSide pk sk (.inl (.inr mc))).run s =
      if progSide then pure (v, (s.1, true))
      else (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc := by
  change (match s.1.1.2 mc with
    | some v => if progSide then pure (v, (s.1, true))
        else (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc
    | none => (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc) = _
  rw [h]

omit [SampleableType Stmt] in
lemma ghostHybridImpl_run_ro_ghost_none (progSide : Bool) (pk : Stmt) (sk : Wit)
    {mc : M × Commit} {s : GhostState M Commit Chal}
    (h : s.1.1.2 mc = none) :
    (ghostHybridImpl ids M maxAttempts progSide pk sk (.inl (.inr mc))).run s =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc := by
  change (match s.1.1.2 mc with
    | some v => if progSide then pure (v, (s.1, true))
        else (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc
    | none => (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc) = _
  rw [h]

omit [SampleableType Stmt] in
lemma ghostHybridImpl_run_sign (progSide : Bool) (pk : Stmt) (sk : Wit)
    (msg : M) (s : GhostState M Commit Chal) :
    (ghostHybridImpl ids M maxAttempts progSide pk sk (.inr msg)).run s =
      (fun alc : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1 := rfl

/-! ### Ghost-value independence of the ghost-blind step (the value-free foundation)

The single structural fact powering the read-bound spine: in the ghost-blind
run the stored ghost *values* are pure write-only side-data. `blindStepProj` forgets exactly
the ghost layer, retaining the run's observable component — the step output, the real cache,
the signed-message list, and the bad flag. `blindStepProj_map_ghostBlindImpl_indep` proves
that this observable projection of one ghost-blind step is *independent of the ghost-layer
values*: any two input ghost layers with the same key domain (same `none`-pattern) produce the
same projected step. The bad flag, the only ghost-derived datum that survives the projection,
fires on ghost-cache *membership* alone, so it depends on the domain, never on the values. -/

/-- The observable projection of a ghost-blind step: forget the ghost cache layer, retaining the
step output, the real cache, the signed-message list, and the bad flag. Written as the explicit
projection lambda so that `Functor.map_map` composes it uniformly with each per-branch handler. -/
def blindStepProj
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) :
    (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t)
        × GhostState M Commit Chal →
      (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t)
        × ((M × Commit →ₒ Chal).QueryCache × List M × Bool) :=
  fun z => (z.1, z.2.1.1.1, z.2.1.2, z.2.2)

omit [SampleableType Stmt] in
/-- **Value-free foundation (Stage 1).** The observable projection (output, real cache, signed
list, bad flag — see `blindStepProj`) of a single ghost-blind step is *independent of the ghost
layer's values*. For any query `t` and any two input ghost layers `gh₁, gh₂` sharing the real
cache `re`, signed list `l`, bad flag `bf`, and key *domain* (`gh₁ q = none ↔ gh₂ q = none`),
the projected step distributions coincide.

This is the manifest output-irrelevance of the stored commitment values in `ghostBlindImpl`,
read off branch-by-branch from the real handler:
* uniform queries leave the ghost layer untouched and never inspect it;
* a random-oracle read answers from the *real* layer via `roStep` on **both** the hit and miss
  branches (`ghostHybridImpl_run_ro_ghost_some` / `ghostHybridImpl_run_ro_ghost_none`, hit branch
  on the Trans side), and only flips the bad flag, whose firing is the membership test
  `mc ∈ dom(gh)` — fixed by the shared domain;
* a signing query runs `ghostSignBody`, whose ghost writes never feed back into the output or
  the real cache (`run_ghostSignBody_fst`: forgetting the ghost layer recovers the accepted-only
  `transSignBody` loop), so the projected step is the same for either input ghost layer.

The ghost values therefore influence neither the run's outputs nor its read points; they are
consulted only to set the bad flag. Stage 2 defers a single signing query's rejected-attempt
commitment draws to a front block on the strength of this independence; Stage 3 lifts the
deferral through the full `simulateQ` fold. -/
lemma blindStepProj_map_ghostBlindImpl_indep (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (re gh₁ gh₂ : (M × Commit →ₒ Chal).QueryCache) (l : List M) (bf : Bool)
    (hdom : ∀ q, gh₁ q = none ↔ gh₂ q = none) :
    blindStepProj M t <$>
        (ghostBlindImpl ids M maxAttempts pk sk t).run (((re, gh₁), l), bf) =
      blindStepProj M t <$>
        (ghostBlindImpl ids M maxAttempts pk sk t).run (((re, gh₂), l), bf) := by
  rw [ghostBlindImpl_eq_ghostHybridImpl_false]
  rcases t with (n | mc) | msg
  · -- Uniform query: the ghost layer is neither read nor written.
    simp only [ghostHybridImpl, StateT.run_mk, blindStepProj, Functor.map_map]
  · -- Random-oracle read: answer is `roStep` on the real layer in both branches; the only
    -- ghost-derived datum is the membership bad flag, fixed by the shared domain.
    change (fun z : Chal × GhostState M Commit Chal => (z.1, z.2.1.1.1, z.2.1.2, z.2.2)) <$>
          (ghostHybridImpl ids M maxAttempts false pk sk (.inl (.inr mc))).run
            (((re, gh₁), l), bf) =
        (fun z : Chal × GhostState M Commit Chal => (z.1, z.2.1.1.1, z.2.1.2, z.2.2)) <$>
          (ghostHybridImpl ids M maxAttempts false pk sk (.inl (.inr mc))).run
            (((re, gh₂), l), bf)
    cases hgh1 : gh₁ mc with
    | none =>
        rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk
              (s := (((re, gh₁), l), bf)) hgh1,
            ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk
              (s := (((re, gh₂), l), bf)) ((hdom mc).1 hgh1)]
        simp [Functor.map_map]
    | some v =>
        have hgh2 : gh₂ mc ≠ none := fun h =>
          Option.some_ne_none v (hgh1 ▸ (hdom mc).2 h)
        obtain ⟨v2, hgh2'⟩ := Option.ne_none_iff_exists'.1 hgh2
        rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk
              (s := (((re, gh₁), l), bf)) hgh1,
            ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk
              (s := (((re, gh₂), l), bf)) hgh2',
            if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
        simp [Functor.map_map]
  · -- Signing query: the ghost writes are forgotten by the projection, and the output plus real
    -- cache are value-free by `run_ghostSignBody_fst`.
    change (fun z : Option (Commit × Resp) × GhostState M Commit Chal =>
            (z.1, z.2.1.1.1, z.2.1.2, z.2.2)) <$>
          (ghostHybridImpl ids M maxAttempts false pk sk (.inr msg)).run (((re, gh₁), l), bf) =
        (fun z : Option (Commit × Resp) × GhostState M Commit Chal =>
            (z.1, z.2.1.1.1, z.2.1.2, z.2.2)) <$>
          (ghostHybridImpl ids M maxAttempts false pk sk (.inr msg)).run (((re, gh₂), l), bf)
    rw [ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg (((re, gh₁), l), bf),
        ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg (((re, gh₂), l), bf)]
    simp only [Functor.map_map]
    have h1 := run_ghostSignBody_fst ids M pk sk msg maxAttempts re gh₁
    have h2 := run_ghostSignBody_fst ids M pk sk msg maxAttempts re gh₂
    calc (fun x : Option (Commit × Resp) ×
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
            (x.1, x.2.1, msg :: l, bf)) <$>
            (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh₁)
        = (fun y : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (y.1, y.2, msg :: l, bf)) <$>
            ((fun zs : Option (Commit × Resp) ×
                ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
                (zs.1, zs.2.1)) <$>
              (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh₁)) := by
          rw [Functor.map_map]
      _ = (fun y : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (y.1, y.2, msg :: l, bf)) <$>
            ((fun zs : Option (Commit × Resp) ×
                ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
                (zs.1, zs.2.1)) <$>
              (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh₂)) := by
          rw [h1, h2]
      _ = _ := by rw [Functor.map_map]

omit [SampleableType Stmt] in
/-- Per-step overlay projection: each step of the Prog-side ghost-instrumented handler
projects onto the corresponding step of the Prog hybrid handler. -/
lemma ghostHybridImpl_proj_prog (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : GhostState M Commit Chal) :
    Prod.map id (fun g : GhostState M Commit Chal =>
        (overlayCache M g.1.1.1 g.1.1.2, g.1.2)) <$>
        (ghostHybridImpl ids M maxAttempts true pk sk t).run s =
      ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (progSignBody ids M pk sk · maxAttempts)) t).run
        (overlayCache M s.1.1.1 s.1.1.2, s.1.2) := by
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, QueryImpl.add_apply_inl, hybridBaseImpl,
      unifFwdImpl, QueryImpl.liftTarget_apply, Functor.map_map]
    rfl
  · refine Eq.trans ?_
      (hybridBaseImpl_run_ro M mc (overlayCache M s.1.1.1 s.1.1.2) s.1.2).symm
    cases hgh : s.1.1.2 mc with
    | some v =>
        rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts true pk sk hgh,
          if_pos rfl,
          roStep_of_some M (overlayCache_apply_ghost_some (M := M) s.1.1.1 hgh)]
        simp
    | none =>
        rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts true pk sk hgh]
        cases hre : s.1.1.1 mc with
        | some v =>
            rw [roStep_of_some M hre, roStep_of_some M (show overlayCache M
              s.1.1.1 s.1.1.2 mc = some v by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1.1 hgh, hre])]
            simp
        | none =>
            rw [roStep_of_none M hre, roStep_of_none M (show overlayCache M
              s.1.1.1 s.1.1.2 mc = none by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1.1 hgh, hre])]
            simp [overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1.1 hgh]
  · refine Eq.trans (b := (fun ac : Option (Commit × Resp) ×
        (M × Commit →ₒ Chal).QueryCache => (ac.1, (ac.2, msg :: s.1.2))) <$>
        (progSignBody ids M pk sk msg maxAttempts).run
          (overlayCache M s.1.1.1 s.1.1.2)) ?_ ?_
    · rw [ghostHybridImpl_run_sign ids M maxAttempts true pk sk msg s,
        ← run_ghostSignBody_overlay ids M pk sk msg maxAttempts s.1.1.1 s.1.1.2]
      refine (Functor.map_map _ _ _).trans (Eq.symm ?_)
      exact (Functor.map_map _ _ _).trans rfl
    · exact (hybridSignImpl_run M (progSignBody ids M pk sk · maxAttempts) msg
        (overlayCache M s.1.1.1 s.1.1.2) s.1.2).symm

omit [SampleableType Stmt] in
/-- Per-step ghost-forgetting projection: each step of the Trans-side ghost-instrumented
handler projects onto the corresponding step of the Trans hybrid handler. -/
lemma ghostHybridImpl_proj_trans (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : GhostState M Commit Chal) :
    Prod.map id (fun g : GhostState M Commit Chal => (g.1.1.1, g.1.2)) <$>
        (ghostHybridImpl ids M maxAttempts false pk sk t).run s =
      ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (transSignBody ids M maxAttempts pk sk)) t).run
        (s.1.1.1, s.1.2) := by
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, QueryImpl.add_apply_inl, hybridBaseImpl,
      unifFwdImpl, QueryImpl.liftTarget_apply, Functor.map_map]
    rfl
  · refine Eq.trans ?_ (hybridBaseImpl_run_ro M mc s.1.1.1 s.1.2).symm
    cases hgh : s.1.1.2 mc with
    | some v =>
        rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh,
          if_neg Bool.false_ne_true]
        exact (Functor.map_map _ _ _).trans rfl
    | none =>
        rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh]
        exact (Functor.map_map _ _ _).trans rfl
  · refine Eq.trans (b := (fun ac : Option (Commit × Resp) ×
        (M × Commit →ₒ Chal).QueryCache => (ac.1, (ac.2, msg :: s.1.2))) <$>
        (transSignBody ids M maxAttempts pk sk msg).run s.1.1.1) ?_ ?_
    · rw [ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg s,
        ← run_ghostSignBody_fst_eq_transSignBody ids M maxAttempts pk sk msg
          s.1.1.1 s.1.1.2]
      refine (Functor.map_map _ _ _).trans (Eq.symm ?_)
      exact (Functor.map_map _ _ _).trans rfl
    · exact (hybridSignImpl_run M (transSignBody ids M maxAttempts pk sk) msg
        s.1.1.1 s.1.2).symm

/-! ## Ghost-domain invariant -/

omit [SampleableType Stmt] in
/-- Support bound for the ghost writes of `ghostSignBody`: every ghost entry of an
output state was either already present or lies at the signed message `msg`. -/
lemma ghostSignBody_support_ghost (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache)
      (z : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)),
      z ∈ support ((ghostSignBody ids M pk sk msg n).run (re, gh)) →
      ∀ q : M × Commit, z.2.2 q ≠ none → gh q ≠ none ∨ q.1 = msg
  | 0, re, gh, z, hz, q, hq => by
    simp only [ghostSignBody, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hq
  | (n + 1), re, gh, z, hz, q, hq => by
    simp only [ghostSignBody, StateT.run_bind, OracleComp.liftM_run_StateT, bind_assoc,
      pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨⟨w, st⟩, -, hz⟩ := hz
    obtain ⟨c, -, hz⟩ := hz
    obtain ⟨oz, -, hz⟩ := hz
    rcases oz with - | zr
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hz
      rcases ghostSignBody_support_ghost pk sk msg n re (gh.cacheQuery (msg, w) c)
          z hz q hq with hgh | hmsg
      · by_cases hqw : q = (msg, w)
        · exact Or.inr (by simp [hqw])
        · exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ hqw] at hgh)
      · exact Or.inr hmsg
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only [uncacheQuery, ne_eq, ite_eq_left_iff, not_forall] at hq
      exact Or.inl hq.2

omit [SampleableType Stmt] in
/-- Ghost-domain invariant: along any run of the ghost-instrumented handlers, every
ghost entry's message component has been recorded in the signed list. -/
lemma ghostHybridImpl_preserves_signed_inv (progSide : Bool) (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : GhostState M Commit Chal)
    (hs : ∀ q : M × Commit, s.1.1.2 q ≠ none → q.1 ∈ s.1.2) :
    ∀ z ∈ support ((ghostHybridImpl ids M maxAttempts progSide pk sk t).run s),
      ∀ q : M × Commit, z.2.1.1.2 q ≠ none → q.1 ∈ z.2.1.2 := by
  intro z hz
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : s.1.1.2 mc with - | v
    · simp only [hgh, support_map] at hz
      obtain ⟨cu, -, rfl⟩ := hz
      exact hs
    · simp only [hgh] at hz
      cases progSide with
      | true =>
          simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hs
      | false =>
          rw [if_neg Bool.false_ne_true, support_map] at hz
          obtain ⟨cu, -, rfl⟩ := hz
          exact hs
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨alc, halc, rfl⟩ := hz
    intro q hq
    rcases ghostSignBody_support_ghost ids M pk sk msg maxAttempts s.1.1.1 s.1.1.2
        alc halc q hq with hgh | hmsg
    · exact List.mem_cons_of_mem _ (hs q hgh)
    · exact hmsg ▸ List.mem_cons_self

end FiatShamirWithAbort
