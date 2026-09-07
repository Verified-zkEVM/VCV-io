/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractability
public import VCVio.CryptoFoundations.MerkleTree.Inductive.QueryBound
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Extractor

/-!
# Unaddressed Merkle extractability specialization

This file exposes the ordinary unaddressed `InductiveMerkleTree` extractability API as a thin
unit-address specialization of `MerkleTreeExtractability`. The canonical stopping-time proof,
source comparison, extractor accounting, and probability numerator live in the generic module.

`unitAddressQueryModel` interprets an ordinary `(left, right)` hash input as a complete query with
address `()`. `extractabilityInner_eq_unaddressed` exposes the concrete unaddressed program for API
inspection. `Adversary` packages its committing and opening phases together with their shared
auxiliary state.

The latter half provides deterministic log-chain collision and extractor-recovery lemmas.
-/

@[expose] public section

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/-! ## Constant-address specialization -/

/-- Complete-query model witnessing the unaddressed tree as the unit-address specialization. -/
def unitAddressQueryModel :
    MerkleTreeExtractability.NodeQueryModel (α × α) Unit α where
  view := Extractor.queryView
  mkQuery _ input := input
  address_mkQuery := by simp [Extractor.queryView]
  input_mkQuery := by intro _ input; rfl

/-- A two-phase adversary for the ordinary unaddressed Merkle extractability game. -/
structure Adversary (α : Type) (s : Skeleton) where
  /-- Auxiliary state carried from the committing phase to the opening phase. -/
  AuxState : Type
  /-- Committing phase: produce a claimed root and auxiliary state. -/
  commit : OracleComp (spec α) (α × AuxState)
  /-- Opening phase: given the auxiliary state, produce a leaf index, claimed leaf value, and
  authentication path. -/
  opening : AuxState → OracleComp (spec α)
    ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)

/-- Forget only the concrete API wrapper, preserving both phases definitionally. -/
abbrev Adversary.toGeneric {s : Skeleton} (𝒜 : Adversary α s) :
    MerkleTreeExtractability.Adversary (α × α) α s where
  AuxState := 𝒜.AuxState
  commit := 𝒜.commit
  opening := 𝒜.opening

/-- The combined committing and opening phases have total query bound `qb`. -/
def Adversary.IsTwoPhaseTotalQueryBound {s : Skeleton}
    (𝒜 : Adversary α s) (qb : ℕ) : Prop :=
  MerkleTreeExtractability.Adversary.IsTwoPhaseTotalQueryBound 𝒜.toGeneric qb

/-- Canonical unaddressed extractability syntax, obtained by unit-address specialization. -/
def extractabilityInner [DecidableEq α] {s : Skeleton} (𝒜 : Adversary α s) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  MerkleTreeExtractability.extractabilityInner unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric

private lemma getPutativeRoot_unitAddress_eq {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leaf : α) (proof : List.Vector α idx.depth) :
    AddressedMerkleTree.getPutativeRootAddressedM
      (fun _ left right => liftM ((spec α).query (left, right))) idx leaf proof =
      getPutativeRoot (m := OracleComp (spec α)) idx leaf proof := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idx ih | ofRight idx ih =>
      simp only [AddressedMerkleTree.getPutativeRootAddressedM, getPutativeRoot]
      rw [ih]
      rfl

/-- Concrete expansion of the canonical specialization in the established unaddressed API. -/
theorem extractabilityInner_eq_unaddressed [DecidableEq α] {s : Skeleton}
    (𝒜 : Adversary α s) :
    extractabilityInner 𝒜 =
      𝒜.commit.withQueryLog >>= fun ((root, aux), queryLog) => do
        let extractedTree := extractor s queryLog root
        let ⟨idx, leaf, proof⟩ ← 𝒜.opening aux
        let extractedProof := generateProof extractedTree idx
        let verified ← verifyProof idx leaf root proof
        return (root, aux,
          ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) := by
  simp [extractabilityInner, MerkleTreeExtractability.extractabilityInner,
    MerkleTreeExtractability.verifyOpening, unitAddressQueryModel,
    getPutativeRoot_unitAddress_eq, Extractor.tree]

/-- Extraction failure means successful verification with a mismatching extracted opening. -/
def OpeningExtractionFailure {s : Skeleton} {AuxState : Type} :
    α × AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop :=
  fun (_, _, ⟨idx, leaf, proof, extractedTree, extractedProof, verified⟩) =>
    verified = true ∧
      (some leaf ≠ extractedTree.get idx.toNodeIndex ∨
        proof.toList.map some ≠ extractedProof.toList)

/-- Shared-random-oracle extractability game for the ordinary unaddressed tree. -/
def extractabilityGame [DecidableEq α] {s : Skeleton} (𝒜 : Adversary α s) :
    OracleComp (spec α) (α × 𝒜.AuxState ×
      ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
       FullData (Option α) s × List.Vector (Option α) idx.depth × Bool)) :=
  (spec α).withCacheOverlay ∅ (extractabilityInner 𝒜)

private theorem openingExtractionFailure_eq_generic
    {s : Skeleton} {AuxState : Type} :
    (OpeningExtractionFailure :
      α × AuxState ×
        ((idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth ×
         FullData (Option α) s × List.Vector (Option α) idx.depth × Bool) → Prop) =
      MerkleTreeExtractability.OpeningExtractionFailure := by
  funext z
  rcases z with ⟨_, _, ⟨_, _, _, _, _, _⟩⟩
  rfl

theorem extractabilityInner_isTotalQueryBound [DecidableEq α] {s : Skeleton}
    (𝒜 : Adversary α s) (qb : ℕ) (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityInner 𝒜) (qb + s.depth) := by
  simpa [extractabilityInner] using
    MerkleTreeExtractability.extractabilityInner_isTotalQueryBound
      unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric qb h

theorem extractabilityGame_isTotalQueryBound [DecidableEq α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ) (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    IsTotalQueryBound (extractabilityGame 𝒜) (qb + s.depth) := by
  simpa [extractabilityGame, extractabilityInner,
    MerkleTreeExtractability.extractabilityGame] using
    MerkleTreeExtractability.extractabilityGame_isTotalQueryBound
      unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric qb h

/-- Exact stopping-time numerator inherited from the query-parametric theorem. -/
def extractabilityROMErrorNumerator (s : Skeleton) (qb : ℕ) : ℕ :=
  MerkleTreeExtractability.extractabilityROMErrorNumerator s qb

theorem extractability_rom_bound [DecidableEq α] [Fintype α] [Inhabited α]
    [IsUniformSpec (spec α)] {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[OpeningExtractionFailure | extractabilityGame 𝒜] ≤
      (extractabilityROMErrorNumerator s qb : ENNReal) *
    (Fintype.card α : ENNReal)⁻¹ := by
  rw [openingExtractionFailure_eq_generic]
  simpa [extractabilityGame, extractabilityInner, extractabilityROMErrorNumerator,
    MerkleTreeExtractability.extractabilityGame] using
    MerkleTreeExtractability.extractability_rom_bound
      unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric qb h

theorem extractability_rom_bound_coarse [DecidableEq α] [Fintype α] [Inhabited α]
    [IsUniformSpec (spec α)] {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb) :
    Pr[OpeningExtractionFailure | extractabilityGame 𝒜] ≤
      ((max ((2 * s.leafCount - 1) * qb) (qb.choose 2) +
        (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card α : ENNReal)⁻¹ := by
  rw [openingExtractionFailure_eq_generic]
  simpa [extractabilityGame, extractabilityInner,
    MerkleTreeExtractability.extractabilityGame] using
    MerkleTreeExtractability.extractability_rom_bound_coarse
      unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric qb h

theorem extractability_rom_bound_birthday_dominates
    [DecidableEq α] [Fintype α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hqb : 2 * (2 * s.leafCount - 1) + 1 ≤ qb) :
    Pr[OpeningExtractionFailure | extractabilityGame 𝒜] ≤
      ((qb.choose 2 + (2 * s.leafCount - 1) * s.depth : ℕ) : ENNReal) *
        (Fintype.card α : ENNReal)⁻¹ := by
  rw [openingExtractionFailure_eq_generic]
  simpa [extractabilityGame, extractabilityInner,
    MerkleTreeExtractability.extractabilityGame] using
    MerkleTreeExtractability.extractability_rom_bound_birthday_dominates
      unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric qb h hqb

theorem extractability_rom_bound_quadratic
    [DecidableEq α] [Fintype α] [Inhabited α] [IsUniformSpec (spec α)]
    {s : Skeleton} (𝒜 : Adversary α s) (qb : ℕ)
    (h : 𝒜.IsTwoPhaseTotalQueryBound qb)
    (hdominance : 2 * (2 * s.leafCount - 1) + 1 ≤ qb)
    (hdepth : 2 * (2 * s.leafCount - 1) * s.depth ≤ qb) :
    Pr[OpeningExtractionFailure | extractabilityGame 𝒜] ≤
      (qb : ENNReal) ^ 2 / (2 * Fintype.card α) := by
  rw [openingExtractionFailure_eq_generic]
  simpa [extractabilityGame, extractabilityInner,
    MerkleTreeExtractability.extractabilityGame] using
    MerkleTreeExtractability.extractability_rom_bound_quadratic
      unitAddressQueryModel (fun _ => ()) 𝒜.toGeneric qb h hdominance hdepth

private lemma singleHash_withQueryLog (a b : α) :
    (singleHash (m := OracleComp (spec α)) a b).withQueryLog =
      (liftM ((spec α).query (a, b)) : OracleComp (spec α) α) >>=
        fun u => pure (u, ([⟨(a, b), u⟩] : (spec α).QueryLog)) := by
  simp [singleHash, OracleComp.withQueryLog_query]

private lemma getPutativeRoot_step_withQueryLog_decompose
    (prog : OracleComp (spec α) α) (mkPair : α → α × α)
    (r : α) (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
      (prog >>= fun a => let (l, r') := mkPair a; singleHash l r').withQueryLog) :
    ∃ a log_a, (a, log_a) ∈ support prog.withQueryLog ∧
      log_v = log_a ++ [⟨mkPair a, r⟩] := by
  simp only [OracleComp.withQueryLog_bind, singleHash_withQueryLog] at hmem
  grind

/-- A structural hash chain in the unaddressed query log. -/
def ChainInLog {s : Skeleton} (log : (spec α).QueryLog) (leaf root : α) :
    (idx : SkeletonLeafIndex s) → List.Vector α idx.depth → Prop
  | .ofLeaf, _ => leaf = root
  | .ofLeft idxLeft, proof =>
      ∃ ancestor : α,
        (⟨(ancestor, proof.head), root⟩ : (_ : α × α) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxLeft proof.tail
  | .ofRight idxRight, proof =>
      ∃ ancestor : α,
        (⟨(proof.head, ancestor), root⟩ : (_ : α × α) × α) ∈ log ∧
        ChainInLog log leaf ancestor idxRight proof.tail

private lemma extractor_internal_eq_of_find?_eq [DecidableEq α]
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root x y : α)
    (h_find : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩) :
    extractor (.internal sl sr) log root =
      FullData.internal (some root) (extractor sl log x) (extractor sr log y) :=
  Extractor.tree_internal_eq_of_find?_eq sl sr log root x y h_find

private lemma extractor_internal_get_eq_none_of_find?_eq_none [DecidableEq α]
    (sl sr : Skeleton) (log : (spec α).QueryLog) (root : α)
    (idx : SkeletonNodeIndex sl ⊕ SkeletonNodeIndex sr)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = none) :
    (extractor (.internal sl sr) log root).get
        (idx.elim SkeletonNodeIndex.ofLeft SkeletonNodeIndex.ofRight) = none := by
  change (Extractor.tree (.internal sl sr) log root).get
    (idx.elim SkeletonNodeIndex.ofLeft SkeletonNodeIndex.ofRight) = none
  rw [Extractor.tree_internal_of_children_eq_none sl sr log root
    (Extractor.children_eq_none_of_find?_eq_none log root hf)]
  cases idx <;>
    exact populateDown_none_get_eq_none (Option.bindPair (Extractor.children log)) rfl _

private lemma chainInLog_mono {s : Skeleton} (idx : SkeletonLeafIndex s)
    {log1 log2 : (spec α).QueryLog} {root leaf : α}
    {proof : List.Vector α idx.depth}
    (h_sub : ∀ q, q ∈ log1 → q ∈ log2)
    (h_chain : ChainInLog log1 leaf root idx proof) :
    ChainInLog log2 leaf root idx proof := by
  induction idx generalizing root with
  | ofLeaf => exact h_chain
  | @ofLeft sl sr idxLeft ih | @ofRight sl sr idxRight ih =>
    obtain ⟨ancestor, h_mem, h_rec⟩ := h_chain
    exact ⟨ancestor, h_sub _ h_mem, ih h_rec⟩

private lemma chainInLog_of_mem_support_getPutativeRoot
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) (r : α)
    (log_v : (spec α).QueryLog)
    (hmem : (r, log_v) ∈ support
        (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof).withQueryLog) :
    ChainInLog log_v leaf r idx proof := by
  induction idx generalizing r log_v with
  | ofLeaf =>
    rw [show (getPutativeRoot (m := OracleComp (spec α))
        SkeletonLeafIndex.ofLeaf leaf proof) = pure leaf from rfl,
      OracleComp.withQueryLog_pure, mem_support_pure_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    rfl
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxLeft leaf proof.tail)
        (fun a => (a, proof.head)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a, log_a, h_rec, rfl⟩ :=
      getPutativeRoot_step_withQueryLog_decompose
        (getPutativeRoot (m := OracleComp (spec α)) idxRight leaf proof.tail)
        (fun a => (proof.head, a)) r log_v hmem
    exact ⟨a, by simp, chainInLog_mono _ (fun _ => List.mem_append_left _)
      (ih proof.tail a log_a h_rec)⟩

/--
If a particular transcript is in the support of a successful `verifyProof` computation
with the query log,
then that log contains a hash chain from `root` down to `leaf`.
-/
private lemma chainInLog_of_mem_support_verifyProof
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf root : α) (proof : List.Vector α idx.depth)
    (log_v : (spec α).QueryLog)
    (hmem : (true, log_v) ∈ support
        (verifyProof (m := OracleComp (spec α)) idx leaf root proof).withQueryLog) :
    ChainInLog log_v leaf root idx proof := by
  grind [ChainInLog, OracleComp.withQueryLog_bind, chainInLog_of_mem_support_getPutativeRoot]

/-- **Log-level binding (Collision Lemma at the log level).** Log-formalized
analog of `getPutativeRootWithHash_binding_collision`: two distinct openings
`(x, proof₁) ≠ (y, proof₂)` of the same `root` at the same index, both
witnessed by hash chains `ChainInLog` in the same `log`, force `log` to
contain a hash collision (two log entries with equal responses but distinct
inputs). -/
theorem logHasCollision_of_chainInLog_of_ne
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root x y : α)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (hne : (x, proof₁) ≠ (y, proof₂))
    (hc₁ : ChainInLog log x root idx proof₁)
    (hc₂ : ChainInLog log y root idx proof₂) :
    LogHasCollision log := by
  induction idx generalizing root x y with
  | ofLeaf =>
    exact absurd (Prod.ext (hc₁.trans hc₂.symm) (List.Vector.ext (fun i => i.elim0))) hne
  | @ofLeft sl sr idxLeft ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (a₁, proof₁.head) = (a₂, proof₂.head)
    · obtain ⟨rfl, hhead⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact Prod.ext rfl (((List.Vector.eq_cons_iff _ _ _).mpr
        ⟨hhead, htail⟩).trans proof₂.cons_head_tail)
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)
  | @ofRight sl sr idxRight ih =>
    obtain ⟨a₁, h₁_mem, hc₁⟩ := hc₁
    obtain ⟨a₂, h₂_mem, hc₂⟩ := hc₂
    by_cases hpair : (proof₁.head, a₁) = (proof₂.head, a₂)
    · obtain ⟨hhead, rfl⟩ := Prod.mk.inj hpair
      refine ih _ _ _ _ _ (fun heq => hne ?_) hc₁ hc₂
      obtain ⟨rfl, htail⟩ := Prod.mk.inj heq
      exact Prod.ext rfl (((List.Vector.eq_cons_iff _ _ _).mpr
        ⟨hhead, htail⟩).trans proof₂.cons_head_tail)
    · exact LogHasCollision.of_mem (fun h => hpair (congrArg Sigma.fst h))
        h₁_mem h₂_mem (heq_of_eq rfl)

/-- Post-IH assembly for the `ofLeft` case of `chainInLog_of_extractor_get_ne_none`.
Given a recursive witness on the left subtree (with ancestor `x`), repackage it
into the witness for the full internal node, using the log entry `⟨(x, y), root⟩`
and consing the sibling `y` onto the extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_left
    [DecidableEq α]
    {sl sr : Skeleton} (idxLeft : SkeletonLeafIndex sl)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxLeft.depth,
        (extractor sl log x).get idxLeft.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sl log x) idxLeft).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf x idxLeft extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofLeft (right := sr) idxLeft)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofLeft (right := sr) idxLeft) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]
  refine ⟨extLeaf, y ::ᵥ extProof, h_extLeaf, ?_, x, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sr log y).getRootValue = some y :=
    Extractor.tree_getRootValue sr log y
  grind [Nat.succ_eq_add_one, List.Vector.toList_cons, SkeletonLeafIndex.depth]

/-- Post-IH assembly for the `ofRight` case of `chainInLog_of_extractor_get_ne_none`.
Symmetric to `chainInLog_of_extractor_internal_step_left`: the recursive witness
lives on the right subtree (ancestor `y`) and the sibling `x` is consed onto the
extracted proof. -/
private lemma chainInLog_of_extractor_internal_step_right
    [DecidableEq α]
    {sl sr : Skeleton} (idxRight : SkeletonLeafIndex sr)
    (log : (spec α).QueryLog) (root x y : α)
    (hf : log.find? (fun ⟨_, r⟩ => r == root) = some ⟨(x, y), root⟩)
    (h_rec : ∃ extLeaf : α, ∃ extProof : List.Vector α idxRight.depth,
        (extractor sr log y).get idxRight.toNodeIndex = some extLeaf ∧
        (generateProof (extractor sr log y) idxRight).toList = extProof.toList.map some ∧
        ChainInLog log extLeaf y idxRight extProof) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α
        (SkeletonLeafIndex.ofRight (left := sl) idxRight).depth,
      (extractor (Skeleton.internal sl sr) log root).get
          (SkeletonLeafIndex.ofRight (left := sl) idxRight).toNodeIndex = some extLeaf ∧
      (generateProof (extractor (Skeleton.internal sl sr) log root)
          (SkeletonLeafIndex.ofRight (left := sl) idxRight)).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root (SkeletonLeafIndex.ofRight (left := sl) idxRight) extProof := by
  obtain ⟨extLeaf, extProof, h_extLeaf, h_extProof, h_chain⟩ := h_rec
  rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]
  refine ⟨extLeaf, x ::ᵥ extProof, h_extLeaf, ?_, y, List.mem_of_find?_eq_some hf, h_chain⟩
  have h_root_value : (extractor sl log x).getRootValue = some x :=
    Extractor.tree_getRootValue sl log x
  grind [Nat.succ_eq_add_one, List.Vector.toList_cons, SkeletonLeafIndex.depth]

/-- **Extractor recovery to a log chain.** When the extractor's path at `idx`
is intact (the value there is `≠ none`), the extracted leaf value and proof
form a hash chain `ChainInLog` in the log. The conclusion bundles three
facts: the extracted leaf (`extLeaf`), the recovered authentication path
(`extProof`), and a chain witness in `log` connecting them to `root`. -/
theorem chainInLog_of_extractor_get_ne_none
    [DecidableEq α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (log : (spec α).QueryLog) (root : α)
    (h_ne_none : (extractor s log root).get idx.toNodeIndex ≠ none) :
    ∃ extLeaf : α, ∃ extProof : List.Vector α idx.depth,
      (extractor s log root).get idx.toNodeIndex = some extLeaf ∧
      (generateProof (extractor s log root) idx).toList = extProof.toList.map some ∧
      ChainInLog log extLeaf root idx extProof := by
  induction idx generalizing root with
  | ofLeaf => exact ⟨root, ⟨[], rfl⟩, rfl, rfl, rfl⟩
  | @ofLeft sl sr idxLeft ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inl idxLeft.toNodeIndex) hf) h_ne_none
    rw [show r = root by grind [find?_eq_some_iff_getElem]] at hf
    exact chainInLog_of_extractor_internal_step_left idxLeft log root x y hf
      (ih x (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))
  | @ofRight sl sr idxRight ih =>
    rcases hf : log.find? (fun ⟨_, r⟩ => r == root) with _ | ⟨⟨x, y⟩, r⟩
    · exact absurd (extractor_internal_get_eq_none_of_find?_eq_none
        sl sr log root (Sum.inr idxRight.toNodeIndex) hf) h_ne_none
    rw [show r = root by grind [find?_eq_some_iff_getElem]] at hf
    exact chainInLog_of_extractor_internal_step_right idxRight log root x y hf
      (ih y (fun he =>
        h_ne_none (by rw [extractor_internal_eq_of_find?_eq sl sr log root x y hf]; exact he)))

end InductiveMerkleTree
