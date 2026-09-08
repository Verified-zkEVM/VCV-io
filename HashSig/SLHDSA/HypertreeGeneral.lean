/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Hypertree
public import HashSig.SLHDSA.Position

/-!
# General SLH-DSA hypertree (FIPS 205 Algorithms 12--13)

This module lifts the established XMSS construction from the one-layer specialization to every
validated SLH-DSA parameter set.  A signature has exactly `d` XMSS components, stored in increasing
layer order.  The signer and root-recovery program share the FIPS low-bits/high-bits position
recurrence.

The layer-zero root recovery in Algorithm 12 is unconditional.  Consequently the `d = 1` signer
performs the discarded recovery prescribed by FIPS even though its layer loop body is empty.
For `d > 1`, the final (top-layer) XMSS signature is not recovered by the signer.

## References

- NIST FIPS 205, Section 7, Algorithms 12--13
-/

@[expose] public section

namespace SLHDSA.GeneralHypertree

open OracleComp

/-- The canonical intrinsic hypertree signature from `Hypertree`.  This namespace introduces the
arbitrary-depth algorithms, not a second representation of their output. -/
abbrev Signature (vp : ValidatedParams) (core : CorePrimitives vp.params) :=
  HtSigCore vp.params core

/-- The base XMSS address at a particular hypertree layer and tree. -/
def layerAdrs (layer tree : ℕ) : Adrs :=
  (Adrs.zero.setLayerAddress layer).setTreeAddress tree

@[simp]
theorem layerAdrs_layer (layer tree : ℕ) : (layerAdrs layer tree).layer = layer := rfl

@[simp]
theorem layerAdrs_tree (layer tree : ℕ) : (layerAdrs layer tree).tree = tree := rfl

/-- A reachable final-layer position uses exactly the unique top-tree address committed by key
generation. -/
theorem LayerPosition.toAdrs_eq_layerAdrs_of_isFinal {vp : ValidatedParams}
    (pos : LayerPosition vp)
    (hfinal : pos.layer.val + 1 = vp.params.d) :
    pos.toAdrs = layerAdrs (vp.params.d - 1) 0 := by
  have hlayer : pos.layer.val = vp.params.d - 1 := by omega
  have htree : pos.tree.val = 0 :=
    LayerPosition.tree_eq_zero_of_isFinal pos hfinal
  simp [LayerPosition.toAdrs, layerAdrs, Adrs.zero, Adrs.setLayerAddress,
    Adrs.setTreeAddress, hlayer, htree]

/-- Typed structural loop for FIPS Algorithm 12.

`recoverFinal` is true only for the `d = 1` entry call. Every non-final component is recovered to
obtain the message signed at the next layer. The loop invariant states that `layers` is exactly the
number of positions from `pos` through the final layer. -/
def signFromPositionWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers)
  | 0, _, _ => pure #v[]
  | 1, _, msg => do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
        return #v[sig]
      else
        return #v[sig]
  | layers + 2, hremaining, msg => do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let root ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
      let next := pos.next (by omega)
      let rest ← signFromPositionWith vp core hash compress nodeHash sk pk false next
        (layers + 1) (by simp [next]; omega) root
      return rest.insertIdx 0 sig

/-- Typed structural loop for FIPS Algorithm 13. It consumes one signature per layer and threads
each recovered XMSS root into the next reachable position. -/
def recoverFromPositionWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (pk : core.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      Vector (XmssSig vp.params core) layers → m core.Y
  -- The zero case only makes the match total: `pos.layer.isLt` contradicts
  -- `pos.layer.val + 0 = d`, so no caller can supply its proof argument.
  | 0, _, msg, _ => pure msg
  | 1, _, msg, sigs =>
      xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sigs.head msg pos.toAdrs
  | layers + 2, hremaining, msg, sigs => do
      let root ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sigs.head msg pos.toAdrs
      let next := pos.next (by omega)
      recoverFromPositionWith vp core hash compress nodeHash pk next (layers + 1)
        (by simp [next]; omega) root sigs.tail

/-! ## Callback-parametric construction -/

/-- FIPS Algorithm 12 for arbitrary positive `d`. -/
def signWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m (Signature vp core) :=
  let pos := LayerPosition.initial vp parts
  signFromPositionWith vp core hash compress nodeHash sk pk (vp.params.d == 1) pos
    vp.params.d (by simp [pos]) msg

/-- Root of the unique top-layer XMSS tree: layer `d - 1`, tree zero. -/
def rootWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) : m core.Y :=
  xmssRootWith core hash compress nodeHash sk pk
    (layerAdrs (vp.params.d - 1) 0)

/-- Recover the public root authenticated by a general hypertree signature. -/
def pkFromSigWith (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m core.Y :=
  let pos := LayerPosition.initial vp parts
  recoverFromPositionWith vp core hash compress nodeHash pk pos vp.params.d
    (by simp [pos]) msg sig

/-! ## Pure typed structural loops -/

/-- Deterministic specialization of FIPS Algorithm 12.  Keeping this structural loop explicit
makes the all-layer correctness induction independent of oracle-program normalization.  The
`recoverFinal` branch records Algorithm 12's mandatory, discarded layer-zero recovery when
`d = 1`; because the interpretation is pure, its value is definitionally discarded. -/
def signFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → prims.Y →
      Vector (XmssSig vp.params prims.core) layers
  | 0, _, _ => #v[]
  | 1, _, msg =>
      let sig := xmssSign prims msg sk pk pos.toAdrs pos.leaf.val
      if recoverFinal then
        let _ := xmssPkFromSig prims pos.leaf.val sig msg pk pos.toAdrs
        #v[sig]
      else
        #v[sig]
  | layers + 2, hremaining, msg =>
      let sig := xmssSign prims msg sk pk pos.toAdrs pos.leaf.val
      let root := xmssPkFromSig prims pos.leaf.val sig msg pk pos.toAdrs
      let next := pos.next (by omega)
      let rest := signFromPosition vp prims sk pk false next (layers + 1)
        (by simp [next]; omega) root
      rest.insertIdx 0 sig

/-- Deterministic specialization of FIPS Algorithm 13 over the same typed trajectory. -/
def recoverFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (pk : prims.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → prims.Y →
      Vector (XmssSig vp.params prims.core) layers → prims.Y
  | 0, _, msg, _ => msg
  | 1, _, msg, sigs =>
      xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs
  | layers + 2, hremaining, msg, sigs =>
      let root := xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs
      let next := pos.next (by omega)
      recoverFromPosition vp prims pk next (layers + 1) (by simp [next]; omega) root sigs.tail

/-! ## Explicit-public-hash programs -/

/-- Explicit-public-hash form of the typed structural signing loop.  This is literally the
callback loop above, specialized to the canonical public-hash queries. -/
def signFromPositionM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      m (Vector (XmssSig vp.params core) layers) :=
  signFromPositionWith vp core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) sk pk recoverFinal pos

/-- Explicit-public-hash form of the typed structural recovery loop.  This shares the callback
implementation used by all other interpretations. -/
def recoverFromPositionM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (pk : core.PkSeed) (pos : LayerPosition vp) :
    (layers : ℕ) → pos.layer.val + layers = vp.params.d → core.Y →
      Vector (XmssSig vp.params core) layers → m core.Y :=
  recoverFromPositionWith vp core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) pk pos

@[simp]
private theorem xmssSignWith_publicHash_eq_xmssSignM
    {p : Params} (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (msg : core.Y) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    xmssSignWith core (PublicHash.f core pk) (PublicHash.tl core pk)
        (PublicHash.h core pk) msg sk pk adrs idx =
      (xmssSignM core msg sk pk adrs idx : m (XmssSig p core)) := rfl

@[simp]
private theorem xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM
    {p : Params} (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (idx : ℕ) (sig : XmssSig p core)
    (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) :
    xmssPkFromSigWith core (PublicHash.f core pk) (PublicHash.tl core pk)
        (PublicHash.h core pk) idx sig msg adrs =
      (xmssPkFromSigM core idx sig msg pk adrs : m core.Y) := rfl

/-- Canonical explicit-public-hash hypertree signer for arbitrary `d`. -/
def signM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m (Signature vp core) :=
  let pos := LayerPosition.initial vp parts
  signFromPositionM vp core sk pk (vp.params.d == 1) pos vp.params.d
    (by simp [pos]) msg

/-- Canonical explicit-public-hash top-root generation for arbitrary `d`. -/
def rootM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) : m core.Y :=
  rootWith vp core (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) sk pk

/-- Canonical explicit-public-hash hypertree recovery for arbitrary `d`. -/
def pkFromSigM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) : m core.Y :=
  let pos := LayerPosition.initial vp parts
  recoverFromPositionM vp core pk pos vp.params.d (by simp [pos]) msg sig

/-- Canonical explicit-public-hash hypertree verification for arbitrary `d`. -/
def verifyM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) : m Bool := do
  let recovered ← pkFromSigM vp core msg sig pk parts
  return decide (recovered = pkRoot)

/-! ## Fixed-answer structural equations -/

/-- Interpreting the explicit-hash structural signer by one fixed total answer function gives
the corresponding pure typed loop. -/
@[simp]
theorem simulateQ_signFromPositionM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    simulateQ answer
        (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg :
          OracleComp (publicHashSpec core) (Vector (XmssSig vp.params core) layers)) =
      signFromPosition vp (PublicHash.withPublicHash core answer) sk pk recoverFinal pos layers
        hremaining msg := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => rfl
  | one =>
      cases recoverFinal <;>
        simp only [signFromPositionM, signFromPositionWith, signFromPosition,
          xmssSignWith_publicHash_eq_xmssSignM,
          xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind, simulateQ_pure,
          simulateQ_xmssSignM_withPublicHash, simulateQ_xmssPkFromSigM_withPublicHash,
          Bool.false_eq_true, ↓reduceIte] <;> rfl
  | more layers _ ih =>
      simp only [signFromPositionM] at ih
      simp only [signFromPositionM, signFromPositionWith, signFromPosition,
        xmssSignWith_publicHash_eq_xmssSignM,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind, simulateQ_pure,
        simulateQ_xmssSignM_withPublicHash, simulateQ_xmssPkFromSigM_withPublicHash, ih]
      rfl

/-- Interpreting the explicit-hash structural recovery loop by one fixed total answer function
gives the corresponding pure typed loop. -/
@[simp]
theorem simulateQ_recoverFromPositionM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (pk : core.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    simulateQ answer
        (recoverFromPositionM vp core pk pos layers hremaining msg sigs :
          OracleComp (publicHashSpec core) core.Y) =
      recoverFromPosition vp (PublicHash.withPublicHash core answer) pk pos layers hremaining
        msg sigs := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => rfl
  | one =>
      simp only [recoverFromPositionM, recoverFromPositionWith, recoverFromPosition,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM,
        simulateQ_xmssPkFromSigM_withPublicHash]
  | more layers _ ih =>
      simp only [recoverFromPositionM] at ih
      simp only [recoverFromPositionM, recoverFromPositionWith, recoverFromPosition,
        xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, simulateQ_bind,
        simulateQ_xmssPkFromSigM_withPublicHash, ih]
      rfl

/-! ## Functional correctness -/

private theorem head_insertIdx_zero {X : Type*} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).head = x := by
  simp [Vector.head, Vector.insertIdx_zero]

private theorem tail_insertIdx_zero {X : Type*} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).tail = rest := by
  rw [Vector.insertIdx_zero]
  apply Vector.ext
  intro i hi
  simp [Vector.tail_eq_cast_extract]

/-- Recovering the result of the typed structural signer reaches the unique top-layer XMSS root,
for every positive validated hypertree depth.  The statement is independent of the initial
digest-derived tree and leaf because the typed position recurrence proves that the final tree is
zero. -/
theorem recoverFromPosition_signFromPosition (vp : ValidatedParams)
    (prims : Primitives vp.params) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : prims.Y) :
    recoverFromPosition vp prims pk pos layers hremaining msg
        (signFromPosition vp prims sk pk recoverFinal pos layers hremaining msg) =
      xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero =>
      have := pos.layer.isLt
      omega
  | one =>
      cases recoverFinal <;>
        change xmssPkFromSig prims pos.leaf.val
          (xmssSign prims msg sk pk pos.toAdrs pos.leaf.val) msg pk pos.toAdrs = _
      all_goals
        rw [xmssPkFromSig_xmssSign prims msg sk pk pos.toAdrs pos.leaf.val pos.leaf.isLt]
        rw [LayerPosition.toAdrs_eq_layerAdrs_of_isFinal pos (by omega)]
  | more layers _ ih =>
      simp only [signFromPosition, recoverFromPosition]
      rw [head_insertIdx_zero, tail_insertIdx_zero]
      rw [xmssPkFromSig_xmssSign prims msg sk pk pos.toAdrs pos.leaf.val pos.leaf.isLt]
      exact ih false (pos.next (by omega)) _ _

/-! ## Naturality -/

/-- Query-preserving monad morphisms commute with the typed structural signer. -/
theorem signFromPositionM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (recoverFinal : Bool)
    (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    F.toMonadHom (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg) =
      signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => simp [signFromPositionM, signFromPositionWith]
  | one =>
      cases recoverFinal <;>
        simp [signFromPositionM, signFromPositionWith,
          xmssSignM_natural core F, xmssPkFromSigM_natural core F]
  | more layers _ ih =>
      simp only [signFromPositionM] at ih
      simp [signFromPositionM, signFromPositionWith, xmssSignM_natural core F,
        xmssPkFromSigM_natural core F, ih]

/-- Query-preserving monad morphisms commute with the typed structural recovery loop. -/
theorem recoverFromPositionM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pk : core.PkSeed) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y)
    (sigs : Vector (XmssSig vp.params core) layers) :
    F.toMonadHom (recoverFromPositionM vp core pk pos layers hremaining msg sigs) =
      recoverFromPositionM vp core pk pos layers hremaining msg sigs := by
  induction layers using Nat.twoStepInduction generalizing pos msg with
  | zero => simp [recoverFromPositionM, recoverFromPositionWith]
  | one => simp [recoverFromPositionM, recoverFromPositionWith,
      xmssPkFromSigM_natural core F]
  | more layers _ ih =>
      simp only [recoverFromPositionM] at ih
      simp [recoverFromPositionM, recoverFromPositionWith,
        xmssPkFromSigM_natural core F, ih]

/-- Query-preserving monad morphisms commute with arbitrary-`d` hypertree signing. -/
theorem signM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    F.toMonadHom (signM vp core msg sk pk parts) = signM vp core msg sk pk parts := by
  exact signFromPositionM_natural vp core F sk pk _ _ _ _ _

/-- Query-preserving monad morphisms commute with top-root generation. -/
theorem rootM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    F.toMonadHom (rootM vp core sk pk) = rootM vp core sk pk := by
  exact xmssRootM_natural core F sk pk (layerAdrs (vp.params.d - 1) 0)

/-- Query-preserving monad morphisms commute with arbitrary-`d` hypertree recovery. -/
theorem pkFromSigM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    F.toMonadHom (pkFromSigM vp core msg sig pk parts) =
      pkFromSigM vp core msg sig pk parts := by
  exact recoverFromPositionM_natural vp core F pk _ _ _ _ _

/-- Query-preserving monad morphisms commute with arbitrary-`d` hypertree verification. -/
theorem verifyM_natural (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m n : Type → Type*} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) :
    F.toMonadHom (verifyM vp core msg sig pk parts pkRoot) =
      verifyM vp core msg sig pk parts pkRoot := by
  simp [verifyM, pkFromSigM_natural vp core F]

/-! ## Pure deterministic interpretations -/

/-- Deterministic general-hypertree signing is the canonical interpretation of `signM`. -/
def sign (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) : Signature vp prims.core :=
  simulateQ (PublicHash.impl prims)
    (signM vp prims.core msg sk pk parts :
      OracleComp (publicHashSpec prims.core) (Signature vp prims.core))

/-- Deterministic top-root generation is the canonical interpretation of `rootM`. -/
def root (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (rootM vp prims.core sk pk : OracleComp (publicHashSpec prims.core) prims.Y)

/-- Deterministic root recovery is the canonical interpretation of `pkFromSigM`. -/
def pkFromSig (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (pkFromSigM vp prims.core msg sig pk parts :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- Deterministic verification is the canonical interpretation of `verifyM`. -/
def verify (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.Y]
    (msg : prims.Y) (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : prims.Y) : Bool :=
  simulateQ (PublicHash.impl prims)
    (verifyM vp prims.core msg sig pk parts pkRoot :
      OracleComp (publicHashSpec prims.core) Bool)

/-! ## Pure API equations and completeness -/

/-- The canonical deterministic signer is exactly the pure typed Algorithm 12 loop. -/
theorem sign_eq_signFromPosition (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    sign vp prims msg sk pk parts =
      let pos := LayerPosition.initial vp parts
      signFromPosition vp prims sk pk (vp.params.d == 1) pos vp.params.d
        (by simp [pos]) msg := by
  unfold sign signM
  rw [simulateQ_signFromPositionM_withPublicHash]
  cases prims
  rfl

/-- The canonical deterministic verifier-side root recovery is exactly the pure typed Algorithm
13 loop. -/
theorem pkFromSig_eq_recoverFromPosition (vp : ValidatedParams)
    (prims : Primitives vp.params) (msg : prims.Y)
    (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    pkFromSig vp prims msg sig pk parts =
      let pos := LayerPosition.initial vp parts
      recoverFromPosition vp prims pk pos vp.params.d (by simp [pos]) msg sig := by
  unfold pkFromSig pkFromSigM
  rw [simulateQ_recoverFromPositionM_withPublicHash]
  cases prims
  rfl

/-- The general-hypertree root — the value FIPS 205 Algorithm 18 publishes as `PK.root` — is
the top-layer XMSS root at tree zero. -/
@[simp]
theorem root_eq_xmssRoot (vp : ValidatedParams) (prims : Primitives vp.params)
    (sk : prims.SkSeed) (pk : prims.PkSeed) :
    root vp prims sk pk = xmssRoot prims sk pk (layerAdrs (vp.params.d - 1) 0) := by
  unfold root rootM rootWith
  change simulateQ (PublicHash.impl prims)
      (xmssRootM prims.core sk pk (layerAdrs (vp.params.d - 1) 0) :
        OracleComp (publicHashSpec prims.core) prims.Y) = _
  exact simulateQ_xmssRootM prims sk pk (layerAdrs (vp.params.d - 1) 0)

/-- Arbitrary-depth hypertree completeness: honest signing and recovery yield the public root. -/
theorem pkFromSig_sign (vp : ValidatedParams) (prims : Primitives vp.params)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    pkFromSig vp prims msg (sign vp prims msg sk pk parts) pk parts = root vp prims sk pk := by
  rw [pkFromSig_eq_recoverFromPosition, sign_eq_signFromPosition, root_eq_xmssRoot]
  exact recoverFromPosition_signFromPosition vp prims sk pk _ _ _ _ _

/-- Deterministic verification is equality with the recovered top root. -/
theorem verify_eq_decide (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : prims.Y) (sig : Signature vp prims.core) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : prims.Y) :
    verify vp prims msg sig pk parts pkRoot =
      decide (pkFromSig vp prims msg sig pk parts = pkRoot) := by
  unfold verify verifyM pkFromSig
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- Honest arbitrary-depth hypertree signatures verify against the top-layer root. -/
theorem verify_sign (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y]
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (parts : DigestParts vp.params) :
    verify vp prims msg (sign vp prims msg sk pk parts) pk parts (root vp prims sk pk) = true := by
  rw [verify_eq_decide, pkFromSig_sign]
  simp

/-! ## Deterministic-handler parity -/

@[simp]
theorem simulateQ_signM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer
        (signM vp core msg sk pk parts :
          OracleComp (publicHashSpec core) (Signature vp core)) =
      sign vp (PublicHash.withPublicHash core answer) msg sk pk parts := by
  simp [sign, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_rootM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    simulateQ answer (rootM vp core sk pk : OracleComp (publicHashSpec core) core.Y) =
      root vp (PublicHash.withPublicHash core answer) sk pk := by
  simp [root, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_pkFromSigM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer
        (pkFromSigM vp core msg sig pk parts : OracleComp (publicHashSpec core) core.Y) =
      pkFromSig vp (PublicHash.withPublicHash core answer) msg sig pk parts := by
  simp [pkFromSig, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_verifyM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    [DecidableEq core.Y]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) (pkRoot : core.Y) :
    simulateQ answer
        (verifyM vp core msg sig pk parts pkRoot : OracleComp (publicHashSpec core) Bool) =
      verify vp (PublicHash.withPublicHash core answer) msg sig pk parts pkRoot := by
  simp [verify, PublicHash.impl_withPublicHash]

/-- Fixed-answer arbitrary-depth hypertree completeness.  Signing, recovery, and top-root
generation are interpreted by one total public-hash answer function. -/
theorem simulateQ_pkFromSigM_signM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer (do
      let sig ← signM vp core msg sk pk parts
      pkFromSigM vp core msg sig pk parts) =
    simulateQ answer (rootM vp core sk pk) := by
  simp only [simulateQ_bind, simulateQ_signM_withPublicHash,
    simulateQ_pkFromSigM_withPublicHash, simulateQ_rootM_withPublicHash]
  exact pkFromSig_sign vp (PublicHash.withPublicHash core answer) msg sk pk parts

/-- Fixed-answer arbitrary-depth hypertree verification completeness.  In particular, the
`d = 1` execution retains Algorithm 12's discarded recovery through `signM`. -/
theorem simulateQ_verifyM_signM_withPublicHash (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (answer : QueryImpl (publicHashSpec core) Id)
    [DecidableEq core.Y]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    simulateQ answer (do
      let pkRoot ← rootM vp core sk pk
      let sig ← signM vp core msg sk pk parts
      verifyM vp core msg sig pk parts pkRoot) = true := by
  simp only [simulateQ_bind, simulateQ_rootM_withPublicHash,
    simulateQ_signM_withPublicHash, simulateQ_verifyM_withPublicHash]
  exact verify_sign vp (PublicHash.withPublicHash core answer) msg sk pk parts

end SLHDSA.GeneralHypertree
