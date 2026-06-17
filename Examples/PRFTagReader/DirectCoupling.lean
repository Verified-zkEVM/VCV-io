/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Table

/-!
# PRF Tag/Reader Protocol — Direct M_ideal/S_ideal Coupling Foundations

Foundations for the direct coupling that identifies the multiple-session ideal world's
cell `(tag, n)` with the reference slot `((tag, 0), n)` of the single-session ideal world.

The two ideal worlds run on different random-oracle tables — `g : TagId × Nonce → Digest` for the
multiple-session world and `gS : (TagId × Fin sessionsPerTag) × Nonce → Digest` for the
single-session world. The coupling map embeds the multiple-session domain into the single-session
domain along the reference session slot `0`, so that the multiple-session table is recovered as a
sub-table of the single-session one.

## Main definitions

* `slotZeroEmbed` — the cell-identification embedding
  `(tag, n) ↦ ((tag, 0), n)` from the multiple-session domain into the single-session domain.
* `slotZeroSubTable` — the multiple-session sub-table of a single-session table obtained by
  precomposing with `slotZeroEmbed`.

## Main results

* `slotZeroEmbed_injective` — the embedding is injective, the prerequisite for marginalization
  of a uniform single-session table onto a uniform multiple-session sub-table.
* `evalDist_slotZeroSubTable_uniformSample` — drawing `gS` uniformly and projecting through
  `slotZeroSubTable` yields the uniform distribution on multiple-session tables. This is the
  eager-form coupling lifting the single-session sampler to a multiple-session sub-sampler.
* `mReaderCellsFinset_image_subset_sReaderCellsFinset` — at any fixed transcript, the
  multiple-side reader cells `{(tag, nonce) | tag ∈ TagId}` embed (via `slotZeroEmbed`) into the
  single-side reader cells `{((tag, sid), nonce) | tag ∈ TagId, sid ∈ Fin sessionsPerTag}` — the
  cell-level inclusion that underlies the slack-free direction of the reader-side bound.
* `mReader_accepts_imp_sReader_accepts` — deterministic reader-side coupling: whenever the
  multiple-session reader accepts a transcript against the sub-table `slotZeroSubTable gS`, the
  single-session reader accepts the same transcript against the full table `gS`. The witness
  `tag` for the multiple side lifts to the witness `(tag, 0)` for the single side.

The `slotZeroEmbed` and `slotZeroSubTable` names are thin, intent-naming aliases over the
established sibling `projectTable`; the distribution and cell-subset lemmas re-derive the
underlying facts in the explicit shape used by the direct coupling argument.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCoupling

variable {TagId Nonce Digest : Type}
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### The cell-identification embedding -/

/-- The cell-identification embedding for the direct M_ideal/S_ideal coupling.

The multiple-session ideal world's domain `TagId × Nonce` embeds into the single-session ideal
world's domain `(TagId × Fin sessionsPerTag) × Nonce` along the reference session slot `0`:
`(tag, n) ↦ ((tag, 0), n)`. -/
@[reducible] def slotZeroEmbed :
    TagId × Nonce → (TagId × Fin sessionsPerTag) × Nonce :=
  fun p => ((p.1, (0 : Fin sessionsPerTag)), p.2)

@[simp] lemma slotZeroEmbed_apply (tag : TagId) (n : Nonce) :
    (slotZeroEmbed (sessionsPerTag := sessionsPerTag) (tag, n)) =
      ((tag, (0 : Fin sessionsPerTag)), n) := rfl

/-- The cell-identification embedding is injective.

This is the prerequisite for marginalization: the reference-slot cells of a single-session table
form a fresh, independent uniform block, reindexed by the multiple-session domain. -/
lemma slotZeroEmbed_injective :
    Function.Injective
      (slotZeroEmbed (TagId := TagId) (Nonce := Nonce) (sessionsPerTag := sessionsPerTag)) := by
  intro p q h
  simp only [slotZeroEmbed, Prod.mk.injEq] at h
  exact Prod.ext h.1.1 h.2

/-! ### Sub-table extraction along the embedding -/

/-- Sub-table extraction: project a single-session random-oracle table
`gS : (TagId × Fin sessionsPerTag) × Nonce → Digest` onto the multiple-session sub-table by
reading the reference session slot `0`, i.e. precompose with `slotZeroEmbed`.

`slotZeroSubTable gS (tag, n) = gS ((tag, 0), n)`. -/
@[reducible] def slotZeroSubTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) : TagId × Nonce → Digest :=
  gS ∘ slotZeroEmbed

@[simp] lemma slotZeroSubTable_apply
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) (tag : TagId) (n : Nonce) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (tag, n) =
      gS ((tag, (0 : Fin sessionsPerTag)), n) := rfl

/-- `slotZeroSubTable` agrees with the sibling `projectTable` from `Table.lean`. -/
lemma slotZeroSubTable_eq_projectTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS =
      projectTable (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS := rfl

/-! ### Eager-table coupling: uniform sub-table from uniform full table -/

/-- **Eager-table coupling.** Drawing a uniform single-session random-oracle table `gS` and
projecting it onto the multiple-session sub-table via `slotZeroSubTable` yields the uniform
distribution on multiple-session tables.

This is the foundational marginalization step of the direct M_ideal/S_ideal coupling: the
reference-slot cells of `gS` are themselves jointly uniform and independent of the off-slot
cells, so the multiple-session sub-table is uniform whenever the single-session full table is. -/
lemma evalDist_slotZeroSubTable_uniformSample
    [Fintype TagId] [DecidableEq TagId]
    [Fintype Nonce] [DecidableEq Nonce]
    [Finite Digest] [Nonempty Digest] [SampleableType Digest] :
    𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>=
        fun gS => pure (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS)] =
      𝒟[$ᵗ (TagId × Nonce → Digest)] :=
  evalDist_uniformSample_map_comp_injective (R := Digest)
    (slotZeroEmbed_injective (TagId := TagId) (Nonce := Nonce)
      (sessionsPerTag := sessionsPerTag))

/-! ### Reader-side cell inclusion under the embedding -/

section ReaderCells

variable [Fintype TagId] [DecidableEq TagId] [DecidableEq Nonce]

/-- Multiple-side reader cells at a fixed transcript: the set of `(TagId × Nonce)` cells that the
multiple-session reader inspects at `transcript`, namely `{(tag, transcript.nonce) | tag}`. -/
def mReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    Finset (TagId × Nonce) :=
  (Finset.univ : Finset TagId).image (fun tag => (tag, transcript.nonce))

/-- Single-side reader cells at a fixed transcript: the set of
`((TagId × Fin sessionsPerTag) × Nonce)` cells the single-session reader inspects at
`transcript`, namely `{((tag, sid), transcript.nonce) | tag, sid}`. -/
def sReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    Finset ((TagId × Fin sessionsPerTag) × Nonce) :=
  (Finset.univ : Finset (TagId × Fin sessionsPerTag)).image
    (fun slot => (slot, transcript.nonce))

/-- **Reader-cell inclusion under the embedding.** At any fixed transcript, the image of the
multiple-side reader cells under `slotZeroEmbed` is contained in the single-side reader cells.

Concretely: every multiple-side cell `(tag, transcript.nonce)` becomes the single-side cell
`((tag, 0), transcript.nonce)`, which is one of the cells the single-side reader inspects (the
`sid = 0` slot). This is the cell-level inclusion that drives the slack-free reader-side bound:
the multiple-side reader inspects strictly fewer cells than the single-side reader. -/
lemma mReaderCellsFinset_image_subset_sReaderCellsFinset
    (transcript : TagTranscript Nonce Digest) :
    (mReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).image
        (slotZeroEmbed (TagId := TagId) (Nonce := Nonce)
          (sessionsPerTag := sessionsPerTag)) ⊆
      sReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) transcript := by
  intro x hx
  simp only [mReaderCellsFinset, sReaderCellsFinset, Finset.mem_image, Finset.mem_univ,
    true_and] at hx ⊢
  obtain ⟨p, ⟨tag, rfl⟩, rfl⟩ := hx
  exact ⟨(tag, (0 : Fin sessionsPerTag)), rfl⟩

/-- Multiple-side reader-cell cardinality: `|TagId|`. -/
lemma card_mReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    (mReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).card = Fintype.card TagId := by
  unfold mReaderCellsFinset
  rw [Finset.card_image_of_injective _
    (fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1), Finset.card_univ]

omit [NeZero sessionsPerTag] in
/-- Single-side reader-cell cardinality: `|TagId| * sessionsPerTag`. -/
lemma card_sReaderCellsFinset (transcript : TagTranscript Nonce Digest) :
    (sReaderCellsFinset (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).card =
        Fintype.card TagId * sessionsPerTag := by
  unfold sReaderCellsFinset
  rw [Finset.card_image_of_injective _
    (fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]

end ReaderCells

/-! ### Reader-side coupling: M acceptance implies S acceptance -/

section ReaderCoupling

variable [Fintype TagId] [DecidableEq Digest]

/-- **Reader-side coupling, deterministic half.** Under the cell-identification embedding
`slotZeroEmbed`, whenever the multiple-session reader (running against the sub-table
`slotZeroSubTable gS`) accepts a transcript, the single-session reader (running against the full
table `gS`) accepts the same transcript.

The proof is purely structural: any multiple-side witness tag `tag` lifts to the single-side
witness `(tag, 0)`, since `slotZeroSubTable gS (tag, n) = gS ((tag, 0), n)` by definition. This is
the first half of the off-bad bound `Pr[M_ideal accept ∧ ¬bad] ≤ Pr[S_ideal accept ∧ ¬bad]` in
the direct M_ideal/S_ideal coupling; no probability or slack is involved. -/
lemma mReader_accepts_imp_sReader_accepts
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest)
    (hM : unlinkReaderAccepts (Slot := TagId)
      (fun tag nonce =>
        slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (tag, nonce))
      (multiplePattern (TagId := TagId) sessionsPerTag) transcript = true) :
    unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
      (fun slot nonce => gS (slot, nonce))
      (singlePattern (TagId := TagId) sessionsPerTag) transcript = true := by
  unfold unlinkReaderAccepts tagAccepts multiplePattern at hM
  unfold unlinkReaderAccepts tagAccepts singlePattern
  simp only [decide_eq_true_eq] at hM ⊢
  obtain ⟨tag, _, hcell⟩ := hM
  exact ⟨tag, (0 : Fin sessionsPerTag), hcell⟩

end ReaderCoupling

/-! ### Compatibility with the sibling eager-form -/

/-- `slotZeroSubTable` agrees with `projectTable` pointwise. Useful for rewriting this module's
direct-coupling statements into the established sibling phrasing in `Table.lean`. -/
@[simp] lemma slotZeroSubTable_eq_projectTable_apply
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) (p : TagId × Nonce) :
    slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS p =
      projectTable (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) gS p := rfl

/-! ### Tag-side coupling: first-session pointwise equality -/

section TagCoupling

variable [DecidableEq TagId] [Fintype TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]

omit [DecidableEq Nonce] in
/-- **Tag-step first-session pointwise equality.** When the queried tag has no prior sessions
(`s.sessionsUsed tag = 0`), the eager-table tag-handler outputs of the multiple-session world
(running against the sub-table `slotZeroSubTable gS`) and the single-session world (running against
the full table `gS`) are equal as `ProbComp` values: both sample a fresh nonce uniformly, look up
the **same** cell `((tag, 0), nonce)` of `gS`, and advance the session counter for `tag` by one.

This is the structural primitive driving the off-bad inequality in the direct M_ideal/S_ideal
coupling. On the first session of a tag, the multiple-side cell `(tag, nonce)` (under the
sub-table view) and the single-side cell `((tag, 0), nonce)` (under the full table) coincide, so
the per-query handler distributions are identical — no probability slack and no bad-event branch.
Subsequent sessions (`sessionsUsed tag ≥ 1`) instead read disjoint cells on the two sides; the
"bad" branch captures precisely that disagreement and is handled separately. -/
lemma multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hzero : s.sessionsUsed tag = 0) :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inl tag) s) =
      singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) gS
        (Sum.inl tag) s := by
  have hslot : s.sessionsUsed tag < sessionsPerTag := by
    rw [hzero]; exact Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)
  rw [multipleTableHandler_tag_run_of_lt _ tag s hslot,
      singleTableHandler_tag_run_of_lt gS tag s hslot]
  refine bind_congr fun nonce => ?_
  -- Both sides sample the same nonce; the cell reads coincide because `sessionsUsed tag = 0`
  -- makes the single-side slot `⟨0, _⟩`, matching the slot-zero embed used by the sub-table.
  have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) =
      (0 : Fin sessionsPerTag) := Fin.ext hzero
  have hcell : gS ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce) =
      slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (tag, nonce) := by
    rw [slotZeroSubTable_apply, hsid]
  rw [hcell]

omit [DecidableEq Nonce] in
/-- **Tag-step first-session pointwise equality, distribution form.** The distribution-level
restatement of the pointwise equality: under `s.sessionsUsed tag = 0`, the two eager-table tag
handlers — run on the sub-table `slotZeroSubTable gS` (multiple side) and on the full table `gS`
(single side) — produce the same output distribution at every fixed `gS`.

This is the per-sample identical-until-bad bind primitive: in a bind chain
`($ᵗ gS) >>= fun gS => multipleTableHandler ... tag s >>= continuation`, the multiple-side bind
is interchangeable with the single-side bind whenever the queried tag has no prior sessions. -/
lemma evalDist_multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : UnlinkState TagId)
    (hzero : s.sessionsUsed tag = 0) :
    𝒟[multipleTableHandler (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inl tag) s] =
      𝒟[singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) gS
          (Sum.inl tag) s] :=
  congrArg evalDist
    (multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero
      gS tag s hzero)

end TagCoupling

/-! ### Reader-step eager-table coupling primitives

The reader-step is deterministic in both worlds: `multipleTableHandler g (Sum.inr transcript) s`
and `singleTableHandler gS (Sum.inr transcript) s` both return `pure (ReaderReply.ofBool …, s)`
with the state untouched. The lemmas in this section bundle that determinism with the
`mReader_accepts_imp_sReader_accepts` cell-level lift to give the bind-friendly forms used by the
direct-coupling induction.

When the M-side reader rejects but the S-side reader accepts (the "M-rejects, S-accepts" gap), the
two `pure`s carry different `ReaderReply`s. The coupling-level inequality therefore cannot be
phrased as a per-step *distribution equality*: any subsequent continuation `f : ReaderReply → …`
of the adversary can branch on the reply and produce arbitrarily different downstream behaviour.
The clean structural statement is instead pointwise on the boolean: at every fixed `gS` and `s`,
M-accept implies S-accept. -/

section ReaderStepCoupling

variable [DecidableEq TagId] [Fintype TagId] [SampleableType Nonce] [DecidableEq Digest]

/-- **Reader-step pure form, multiple side.** The multiple-session reader handler against the
sub-table `slotZeroSubTable gS` returns a pure `ReaderReply.ofBool` of the M-side acceptance
predicate, with the state untouched. Restatement of `multipleTableHandler_reader_run` with the
sub-table substituted, in the explicit shape used by the direct-coupling induction. -/
lemma multipleTableHandler_reader_run_slotZeroSubTable
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag)
      (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce =>
          slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (tag, nonce))
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript), s) :=
  multipleTableHandler_reader_run (sessionsPerTag := sessionsPerTag)
    (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) transcript s

/-- **Reader-step ordered coupling.** At any fixed single-session table `gS`, transcript, and
state, the M-side reader reply (against the sub-table `slotZeroSubTable gS`) and the S-side reader
reply (against the full table `gS`) satisfy `M-reply = .ok → S-reply = .ok`.

This is the deterministic-half "M-accept implies S-accept" lift
`mReader_accepts_imp_sReader_accepts`, repackaged at the reader-handler level. It is the
per-step ingredient the direct-coupling induction uses to charge
the reader-step's potential bool disagreement to nothing (M-side accept always lifts) — the only
gap is "M rejects, S accepts", which is absorbed in the direction of the headline inequality
`Pr[M accept] ≤ Pr[S accept]`. -/
lemma multipleReader_reply_imp_singleReader_reply
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (hM : unlinkReaderAccepts (Slot := TagId)
      (fun tag nonce =>
        slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS (tag, nonce))
      (multiplePattern (TagId := TagId) sessionsPerTag) transcript = true) :
    (multipleTableHandler (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag) gS) (Sum.inr transcript) s) =
      singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest) gS
        (Sum.inr transcript) s := by
  rw [multipleTableHandler_reader_run_slotZeroSubTable,
      singleTableHandler_reader_run gS transcript s, hM,
      mReader_accepts_imp_sReader_accepts gS transcript hM]

end ReaderStepCoupling

/-! ### Composition

The pieces above — the eager-table sub-sampler `evalDist_slotZeroSubTable_uniformSample`, the
deterministic reader lift `mReader_accepts_imp_sReader_accepts`, and the tag-step first-session
equality `multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero` — are
composed in `DirectCoupling/Compose.lean` by the eager-form induction
`multipleBadEager_le_singleEager_DC_aux` and the lazy-form headline
`multipleIdeal_le_singleIdeal_add_bad_DC` (the hdist-free multiple-to-single bound). This module
deliberately stops at the per-step structural primitives. -/

end DirectCoupling

end PRFTagReader
