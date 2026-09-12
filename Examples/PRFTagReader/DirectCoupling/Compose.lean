/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.DirectCoupling
public import Examples.PRFTagReader.DirectCoupling.StepLemmas
public import Examples.PRFTagReader.DirectCoupling.Swap
public import Examples.PRFTagReader.DirectCoupling.ReaderCase
public import Examples.PRFTagReader.DirectCoupling.TagSlotPositive
public import Examples.PRFTagReader.DirectCoupling.TagSlotZero
public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup

/-!
# PRF Tag/Reader Protocol — Direct M_ideal/S_ideal Coupling, Headline Composition

This module composes the per-step direct-coupling primitives from
`Examples.PRFTagReader.DirectCoupling` (the `slotZeroEmbed` / `slotZeroSubTable` cell
identification, the sub-table uniform sampler, the deterministic reader lift, and the
first-session tag-step equality) into the headline bound

```
Pr[multipleIdealQueryImpl true] ≤
  Pr[singleIdealQueryImpl true] + Pr[bad]
    + qReader·|TagId| / |Digest| + qReader·qTag / |Nonce|
    + qReader·|TagId|·sessionsPerTag / |Digest|
```

for every adversary, with no distinctness hypothesis on its reader nonces. The bound carries no
tag-side slack term: removing the reader-nonce distinctness hypothesis costs zero extra slack
compared with the conditional version, because the tag-side cell-count gap is absorbed by
`le_self_add` at every tag step.

The direct coupling identifies the multiple-session world's RO cell `(tag, n)` with the
single-session world's reference-slot cell `((tag, 0), n)` via `slotZeroEmbed` /
`slotZeroSubTable`. Under this identification:

* **Tag step, slot 0.** Both worlds read the cell `((tag, 0), n)` of a shared `gS` — identical
  step (`multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero`).
* **Tag step, slot ≥ 1.** M reads `gS((tag, 0), n)` (sub-table); S reads `gS((tag, k), n)` —
  independent uniforms off a nonce collision. The `multipleBadAdvance` bad flag captures the
  nonce-collision case; off-bad, the per-step output distributions agree marginally because
  both reads are fresh uniforms.
* **Reader step.** Only the slot-0 column at the queried nonce is lazified on both sides, so the M
  reader bit collapses to a deterministic bit `m` of the resulting cache while slot-positive cells
  stay uncached. M-accept implies S-accept (`mReader_accepts_imp_sReader_accepts`), and this
  implication is one-sided: when `m` is `true` both sides continue with the same reply, and when
  `m` is `false` the S-side's slot-positive collision branch is *discarded* over `ℝ≥0∞`, charging
  only the collision event's uniform mass `≤ |TagId| · sessionsPerTag / |Digest|` per reader query.

## Main results

* `multipleBadEager_le_singleEager_DC_aux` — eager-form direct coupling aux, by structural
  induction on the adversary, coupling the multiple-session world directly to the single-session
  world with no distinctness hypothesis on the reader nonces.
* `multipleIdeal_le_singleIdeal_add_bad_DC` — lazy-form headline, the standard eagerization of the
  eager-form aux, again with no reader-nonce distinctness hypothesis.

## Layout

The eager-form aux `multipleBadEager_le_singleEager_DC_aux` is a thin dispatcher over the
induction on the adversary: the `pure` and slot-exhausted tag cases close inline, while the three
large induction cases live in sibling files and are invoked with the induction hypothesis as an
explicit premise.

* `Examples.PRFTagReader.DirectCoupling.ReaderCase` (`dcAux_reader_step`) — the asymmetric-discard
  reader (`Sum.inr transcript`) step.
* `Examples.PRFTagReader.DirectCoupling.TagSlotPositive` (`dcAux_tag_slotPositive`) — the
  slot-positive tag (`Sum.inl tag`, `1 ≤ sessionsUsed < sessionsPerTag`) step.
* `Examples.PRFTagReader.DirectCoupling.TagSlotZero` (`dcAux_tag_slotZero`) — the slot-zero tag
  (`Sum.inl tag`, `sessionsUsed = 0`) step.

The downstream wrappers (the lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC`, slack-term
packaging) are thin compositions.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory

namespace PRFTagReader

section DirectCouplingCompose

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

namespace UnlinkReduction

/-! ### Eager-form direct-coupling aux

The structural induction over the adversary, coupling M-side
`multipleBadTableHandler (slotZeroSubTable gS)` (with `UnlinkBadState` instrumentation) against
S-side `singleTableHandler gS` over a shared single-session RO table `gS`. M is coupled directly to
S via the slot-0 sub-table embedding, with no intermediate hybrid world.

The aux is deliberately formulated in terms of *eager* table handlers and a *shared* draw `$ᵗ gS`;
the lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC` below recovers it via the standard
eagerization equivalences. -/

omit [Nonempty TagId] in
/-- **Direct M-S coupling aux (eager).** Under a shared `$ᵗ gS` sample, the eager-form fine handler
`multipleBadTableHandlerFine (slotZeroSubTable (tableExtending c gS))` (with `UnlinkBadState`
instrumentation) success probability is bounded by the eager-form `singleTableHandler
(tableExtending c gS)` success probability, plus the multiple-bad `bad`-probability, plus three
additive slacks: `qR·|TagId|/|Digest|`, `qRInit·qT/|Nonce|`, and
`qR·|TagId|·sessionsPerTag/|Digest|`.

The tag-side cell-count gap costs zero extra slack: at every tag step (slot 0 and slot positive)
the per-step `|TagId|·sessionsPerTag/|Digest|` carve is dropped via `le_self_add` (cell-pair
independence provides per-`n` equality off the bad flag), so removing the reader-nonce distinctness
hypothesis is free on the tag side. The genuinely charged slacks are: `qRInit·qT/|Nonce|`, charged
at slot-positive tag steps via the reader-touched-set membership event `R.card/|Nonce|`
(`probEvent_bind_le_add_bad_disagree` with `D = (· ∈ R)`); and `qR·|TagId|·sessionsPerTag/|Digest|`,
charged at the asymmetric-discard reader step via `probEvent_cacheBadReader_uniformSample_le`. The
reader-cell slack `qR·|TagId|/|Digest|` is carried as headroom for the per-query reader split.

The coupling is hypothesis- and invariant-free at the eager level: no reader-nonce distinctness
hypothesis, no cache-coupling invariant, and no collision-freshness predicate. The bound is
established by structural induction over the adversary `oa`:

* **Tag steps.** The slot-0 sub-table embedding is fixed (independent of state); at slot 0 the M
  and S tag responses agree pointwise. Slot-positive tag divergence is captured by the
  `multipleBadAdvance` bad flag — off-bad, M and S produce statistically identical fresh uniforms
  despite reading different cells. The per-nonce disagreement is split on membership in `R`, the
  set of reader-touched nonces: off `R` the response invariant `hRespInv` carries the closed
  argument through, and the on-`R` mass is charged to the `qRInit·qT/|Nonce|` slack.
* **Reader steps.** Only the slot-0 column at the queried nonce is lazified on both sides (via
  `idealCacheMapM` over the cells `{((T,0), nonce) : T}`), extending the cache `c → c₀` while
  leaving slot-positive cells uncached so the strong cache invariant `hcInv` survives. The M
  reader bit then collapses to a deterministic bit `m` of `c₀`. When `m = true` the S reader also
  accepts (the slot-0 witness lifts), both sides continue with the same reply, and the induction
  hypothesis at `(c₀, qR', R ∪ {nonce})` closes the step. When `m = false`, M rejects; the asymmetry
  `mAcc ⟹ sAcc` is one-sided, so over `ℝ≥0∞` the S-side's slot-positive collision branch is
  *discarded*: the actual S reader bit equals `cacheBadReader gS`, and replacing it by the constant
  `false` reply costs exactly the collision event `E gS := ∃ T sid ≠ 0, gS ((T,sid), nonce) = auth`,
  whose uniform mass `≤ |TagId|·sessionsPerTag/|Digest|` is charged to a single slack unit.

The first-time-per-nonce bookkeeping is threaded through `qRInit`, `R`, and `hqRle : qR + R.card ≤
qRInit`: each reader query inserts its nonce into `R`, and the reader-drawn slot-0 cache entries
only break `hRespInv` off `R`, which the gated form `hRespInv` (conditioned on `n ∉ R`) absorbs.

The aux is deliberately formulated in terms of eager table handlers and a shared draw `$ᵗ gS`; the
lazy headline `multipleIdeal_le_singleIdeal_add_bad_DC` recovers it via the standard eagerization
equivalences. -/
lemma multipleBadEager_le_singleEager_DC_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT qRInit : ℕ)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (R : Finset Nonce)
    (hqR : OracleComp.IsQueryBoundP oa (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (·.isLeft) qT)
    (hqRle : qR + R.card ≤ qRInit)
    (hcInv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
        ∀ n : Nonce, c ((tag, sid), n) = none)
    (hRespInv : ∀ tag : TagId, ∀ n : Nonce, n ∉ R →
        c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
        sB.responses (tag, n) ≠ none) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine) oa).run (s, sB)] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)) oa).run' s] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine) oa).run (s, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  -- Induction cases: pure / tag slot-zero / tag slot-positive / tag slot-exhausted / reader.
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT s c sB R hqRle hcInv hRespInv with
  | pure b =>
    -- Pure case: both sides collapse the `simulateQ` to `pure b`. After `simp`, the LHS
    -- becomes `do gS ← $ᵗ; gFine ← $ᵗ; pure b` (`bind_const` shape since `pure b` ignores
    -- `gFine`). Collapse the inner `gFine ← $ᵗ; pure b` via `probOutput_bind_const` and the
    -- uniform `Pr[⊥ | $ᵗ ·] = 0` identity (`probFailure_uniformSample`) so the inner factor
    -- becomes `1 * Pr[= true | (fun _ => b) <$> $ᵗ ·]`. Bad + 3 slacks are nonnegative, dropped
    -- via `le_add_right`.
    simp only [simulateQ_pure, StateT.run_pure, StateT.run'_eq, map_pure, bind_pure_comp,
      probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
    refine le_add_right (le_add_right (le_add_right (le_add_right ?_)))
    rfl
  | query_bind t k ih =>
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · by_cases hzero : s.sessionsUsed tag = 0
        · -- Slot-zero tag case. Delegated to `dcAux_tag_slotZero`, which takes the induction
          -- hypothesis `ih` as an explicit premise.
          exact dcAux_tag_slotZero qRInit qR qT s c sB R hqRle hcInv hRespInv tag k ih
            hqR hqT hslot hzero
        · -- Slot-positive tag case. Delegated to `dcAux_tag_slotPositive`, which takes the
          -- induction hypothesis `ih` as an explicit premise.
          exact dcAux_tag_slotPositive qRInit qR qT s c sB R hqRle hcInv hRespInv tag k ih
            hqR hqT hslot hzero
      · -- Slot-exhausted tag case. Both M-Fine and S handlers return `pure (none, s, sB)` /
        -- `pure (none, s)` (since `multipleBadAdvance tag sB none = sB` and `gFine` is not
        -- consumed by the tag branch). The head step unfolds to `pure none` on both sides; the
        -- inner `gFine ← $ᵗ` binder is consumed via `bind_const` shape. After splitting
        -- `qT = qT' + 1`, the IH at `qT'` applies directly with unchanged state `(s, sB)`; the
        -- `qT`-bearing nonce-aliasing slack (qRInit*qT/|Nonce|) weakens back via `gcongr`.
        have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR := by
          have := hqR
          rw [OracleComp.isQueryBoundP_query_bind_iff] at this
          simpa using this.2
        have hqTsplit := hqT
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
        have hqTpos : 0 < qT := hqTsplit.1.resolve_left (fun h => absurd rfl h)
        obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
        have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT' := fun u => by
          simpa using hqTsplit.2 u
        -- M-Fine step under `hslot`: returns `pure (none, s, sB)` (no `gFine` dependence;
        -- `multipleBadAdvance tag sB none = sB`).
        have hMstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            ∀ gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest,
            multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) gFine (Sum.inl tag) (s, sB)
            = pure (none, s, sB) := by
          intro gS gFine
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) (Sum.inl tag)) s
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1))
              = _
          rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
          rfl
        -- S step under `hslot`: returns `pure (none, s)`.
        have hSstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
              (Sum.inl tag) s
            = pure (none, s) := fun gS =>
          singleTableHandler_tag_run_of_not_lt (OracleComp.tableExtending c gS) tag s hslot
        -- Rewrite each of the three positions (LHS-success, RHS-success, BAD-event) so the head
        -- step collapses to running `k none` at the unchanged state. Both M-Fine and S handlers
        -- under `hslot` return `pure (none, …)`, so `pure_bind` reduces the head bind.
        have hLHS_eq :
            (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    z.1) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
            = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k none)).run (s, sB)) := by
          refine bind_congr fun gS => ?_
          refine bind_congr fun gFine => ?_
          rw [multipleBadTableFine_run_query_bind', hMstep gS gFine]
          simp only [unlinkOracleSpec_range_inl, pure_bind]
        have hRHS_eq :
            (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS))
                  (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s)
            = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c gS)) (k none)).run' s) := by
          refine bind_congr fun gS => ?_
          rw [singleTable_run'_query_bind', hSstep gS]
          exact pure_bind _ _
        have hBAD_eq :
            (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c gS)) gFine)
                    (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))
            = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending c gS)) gFine) (k none)).run (s, sB)) := by
          refine bind_congr fun gS => ?_
          refine bind_congr fun gFine => ?_
          rw [multipleBadTableFine_run_query_bind', hMstep gS gFine]
          simp only [unlinkOracleSpec_range_inl, pure_bind]
        rw [probOutput_congr rfl (congrArg evalSPMF hLHS_eq),
            probOutput_congr rfl (congrArg evalSPMF hRHS_eq),
            probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalSPMF hBAD_eq)]
        -- Now LHS / RHS / BAD all evaluate `k none` at the unchanged state `(s, sB)`. Apply IH at
        -- `qT'`; the `qT`-bearing nonce-aliasing slack weakens back via `gcongr` + `Nat.le_succ`.
        refine (ih none qR qT' s c sB R (hqRk none) (hqTk none) hqRle hcInv hRespInv).trans ?_
        gcongr
        exact Nat.le_succ _
    | inr transcript =>
      -- Reader case: the asymmetric-discard step. Delegated to `dcAux_reader_step`, which takes
      -- the induction hypothesis `ih` as an explicit premise.
      exact dcAux_reader_step qRInit qR qT s c sB R hqRle hcInv hRespInv transcript k ih hqR hqT

end UnlinkReduction

/-! ### Lazy-form headline

The lazy-form multiple-vs-single ideal-world bound, holding for every adversary with no
distinctness hypothesis on its reader nonces. Routes through
`multipleBadEager_le_singleEager_DC_aux` via the standard eagerization equivalences for the
multiple-bad handler (`evalSPMF_simulateQ_multipleBadQueryImpl_run_eq_tableExtending`) and the
single-ideal handler (`probOutput_singleIdeal_run'_eq_tableSample`). -/

namespace UnlinkReduction

omit [Nonempty TagId] in
/-- **Multi-to-single via direct M-S coupling.** Bounds the multiple-session ideal world by the
single-session ideal world plus the multiple-bad collision probability and three unconditional
slack terms, for every adversary and with no distinctness hypothesis on its reader nonces. None of
the slacks is tag-side: the tag-side cell-count gap is absorbed by `le_self_add` at every tag step,
so removing the reader-nonce distinctness hypothesis costs zero extra slack.

The direct M-S coupling via `slotZeroSubTable` works
unconditionally on the adversary (no nonce-distinctness assumption) because the per-step
identification of M's cell `(tag, n)` with S's cell `((tag, 0), n)` is a fixed embedding, not a
state-dependent one. The bound is supplied by `multipleBadEager_le_singleEager_DC_aux`, lifted to
the lazy ideal handlers by the standard eagerization equivalences and instantiated at `R = ∅`,
`qRInit = qReader`. -/
theorem multipleIdeal_le_singleIdeal_add_bad_DC [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- **Step 1.** Replace the multiple-ideal LHS by the multiple-bad LHS (same `Pr[= true]`).
  rw [← probOutput_multipleBad_run'_eq_multipleIdeal adversary
      (UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)) UnlinkBadState.init]
  -- **Step 2.** Eagerize the M-side: the lazy `multipleBadQueryImpl` run distribution equals the
  -- `$ᵗ gM`-then-eager-table form, modulo the `(z.1, z.2.2)` map projection.
  have hM := evalSPMF_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    (sessionsPerTag := sessionsPerTag) adversary
    UnlinkState.init (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init
  -- M-side success-term rewrite: factor `run' = (·.1) <$> run` through `(z.1, z.2.2) <$> run`.
  have hMsucc :
      Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
          ((UnlinkState.init, (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)),
            UnlinkBadState.init)] =
      Pr[= true | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending
                (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] := by
    apply probOutput_congr rfl
    have h := congrArg (fun d => (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$> d) hM
    simpa only [StateT.run'_eq, ← evalSPMF_map, Functor.map_map, map_bind,
      Function.comp_def] using h
  -- M-side bad-term rewrite: factor `z.2.2.bad = (z.2.bad) ∘ (z.1, z.2.2)` and apply `hM`.
  have hMbad :
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending
              (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache) gM)) adversary).run
            (UnlinkState.init, UnlinkBadState.init)] := by
    have hbadev :
        (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad = true) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
            (z.1, z.2.2)) := rfl
    rw [hbadev, ← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) hM
  -- **Step 3.** Eagerize the S-side success term to `$ᵗ gS >>= singleTableHandler gS`.
  rw [hMsucc, hMbad, probOutput_singleIdeal_run'_eq_tableSample adversary]
  -- Collapse `tableExtending ∅ g = g` on both M (over `TagId × Nonce`) and S (over the
  -- `(TagId × Fin sp) × Nonce` domain) sides.
  simp only [OracleComp.tableExtending_empty]
  -- **Step 4.** Bridge `$ᵗ (TagId × Nonce → Digest)` to
  -- `$ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)` via `slotZeroSubTable`. The bridge says:
  -- for any continuation `F`, the distribution of `$ᵗ gM >>= F gM` equals the distribution of
  -- `$ᵗ gS >>= F (slotZeroSubTable gS)`. We package this as a generic helper and apply it twice
  -- (once for the success term, once for the bad term).
  have : Nonempty Digest :=
    ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hbridge : ∀ {X : Type} (F : (TagId × Nonce → Digest) → ProbComp X),
      𝒮[($ᵗ (TagId × Nonce → Digest)) >>= F] =
      𝒮[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)] := by
    intro X F
    let : MeasurableSpace Digest := ⊤
    let : MeasurableSpace X := ⊤
    apply evalSPMF_eq_of_evalDist_eq
    have hSZ := evalDist_slotZeroSubTable_uniformSample
      (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      evalDist_uniformSample evalDist_uniformSample
    have hR : (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => F (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS))
        = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
            fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) >>= F := by
      simp
    rw [hR, evalDist_bind_of_discrete _ F, evalDist_bind_of_discrete _ F, hSZ]
  -- M-success bridge.
  have hbridge_succ :
      Pr[= true | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gM) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] =
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] :=
    probOutput_congr rfl (hbridge _)
  -- M-bad bridge.
  have hbridge_bad :
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) gM) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (hbridge _)
  rw [hbridge_succ, hbridge_bad]
  -- **Step 4b.** Fine-shape bridges. The aux's signature carries an outer
  -- `gFine ← $ᵗ ((TagId × Fin sp) × Nonce → Digest)` binder and the Fine handler
  -- `multipleBadTableHandlerFine ... gFine`. Bridge the coarse-shape LHS-success and
  -- RHS-bad terms (the current goal shapes after `rw [hbridge_succ, hbridge_bad]`) to the
  -- Fine-shape via `evalSPMF_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq`.
  -- Per-`gS`, the bridge gives `𝒮[(π <$> gFine←$ᵗ; Fine.run p)] = 𝒮[coarse.run p]` where
  -- `π = fun z => (z.1, z.2.1, {z.2.2 with cacheBad := p.2.cacheBad})`. Both `Bool.fst` and the
  -- bad event `z.2.bad` factor through `π` (they ignore `cacheBad`).
  have hFineEq : ∀ (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest),
      𝒮[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad :=
              (UnlinkBadState.init : UnlinkBadState TagId Nonce Digest).cacheBad})) <$>
            (do let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                    (UnlinkState.init, UnlinkBadState.init))]
        = 𝒮[(simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
              (UnlinkState.init, UnlinkBadState.init)] := fun gS =>
    evalSPMF_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq
      (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) adversary
      ((UnlinkState.init, UnlinkBadState.init) :
        UnlinkState TagId × UnlinkBadState TagId Nonce Digest)
  -- Apply the Fine bridge to the success term (event factors through π since π preserves `z.1`).
  have hsucc_fine :
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
      Pr[= true | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    refine probEvent_bind_congr' _ _ fun gS => ?_
    have h := probEvent_congr' (p := fun z => z.1 = true)
      (fun _ _ => Iff.rfl) (hFineEq gS).symm
    simpa only [← map_bind, probEvent_map, Function.comp_def] using h
  -- Apply the Fine bridge to the bad term. The bad event factors through π (cacheBad ≠ bad).
  -- Strategy: use `probEvent_bind_congr'` to reduce to a per-gS equality, then push the
  -- `(z.1, z.2.2)` map through `probEvent_map` to expose the `z.2.2.bad` predicate, then
  -- apply `hFineEq` after observing that the bad predicate is π-invariant.
  have hbad_fine :
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) gFine) adversary).run
                (UnlinkState.init, UnlinkBadState.init)] := by
    refine probEvent_bind_congr' _ _ fun gS => ?_
    have h := probEvent_congr' (p := fun z => z.2.2.bad = true)
      (fun _ _ => Iff.rfl) (hFineEq gS).symm
    simpa only [← map_bind, probEvent_map, Function.comp_def] using h
  rw [hsucc_fine, hbad_fine]
  -- **Step 5.** Apply the DC aux at `c = ∅`, `s = UnlinkState.init`, `sB = UnlinkBadState.init`.
  have haux := multipleBadEager_le_singleEager_DC_aux (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag qReader UnlinkState.init
    (∅ : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) UnlinkBadState.init ∅
    hqReader hqTag (by simp) (fun _ _ _ _ => rfl) (fun _ _ _ h => absurd rfl h)
  simp only [OracleComp.tableExtending_empty] at haux
  -- The aux bound is term-by-term equal to the headline RHS: the three eager slacks match exactly.
  exact haux

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
