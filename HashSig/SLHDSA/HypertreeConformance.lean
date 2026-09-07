/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.HypertreeGeneral

/-!
# Hypertree callback refinement and trajectory conformance

The callback APIs and explicit public-hash programs use one hypertree control flow. The bridge
theorems in this module expose that refinement boundary without introducing another signer, while
the trace API records the exact FIPS 205 layer/tree/leaf trajectory.

## References

- NIST FIPS 205, Section 7, Algorithms 12--13
-/

@[expose] public section

namespace SLHDSA

namespace GeneralHypertree

/-! ## Arbitrary-depth callback refinement -/

/-- Exact depth-one callback schedule: Algorithm 12 recovers the sole XMSS signature and discards
the result before returning it. This is a compile-time witness of the FIPS-mandated discarded
recovery at the loop-level callback API — the pure interpretations are blind to it and every
query-count theorem is only an upper bound; `DepthOneCompatibility.signM_toOneLayer_eq`
witnesses the same schedule at the scheme level. -/
theorem signFromPositionWith_one_recover (vp : ValidatedParams)
    (core : CorePrimitives vp.params) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 1 = vp.params.d) :
    signFromPositionWith vp core hash compress nodeHash sk pk true pos 1 hremaining msg = (do
      let sig ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let _ ← xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig msg pos.toAdrs
      return #v[sig]) := by
  rfl

/-- Exact two-layer callback schedule: the first XMSS root becomes the top-layer message, while
the top signature is returned without an additional discarded recovery — the compile-time
witness of Algorithm 12's `j < d - 1` recovery guard. -/
theorem signFromPositionWith_two (vp : ValidatedParams)
    (core : CorePrimitives vp.params) {m : Type → Type*} [Monad m] [LawfulMonad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 2 = vp.params.d) :
    signFromPositionWith vp core hash compress nodeHash sk pk false pos 2 hremaining msg = (do
      let sig0 ← xmssSignWith core hash compress nodeHash msg sk pk pos.toAdrs pos.leaf.val
      let root0 ←
        xmssPkFromSigWith core hash compress nodeHash pos.leaf.val sig0 msg pos.toAdrs
      let next := pos.next (by omega)
      let sig1 ← xmssSignWith core hash compress nodeHash root0 sk pk next.toAdrs next.leaf.val
      return #v[sig0, sig1]) := by
  simp [signFromPositionWith]

/-- Callback-parametric general hypertree signing is the canonical explicit-query signer after
instantiating the three public-hash callbacks. This theorem is intentionally not a simp rule: it
marks an API boundary rather than choosing a global normal form. -/
theorem signWith_publicHash_eq_signM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    signWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        msg sk pk parts = signM vp core msg sk pk parts := rfl

/-- Callback-parametric top-root generation is the canonical explicit-query key-generation root
after instantiating the three public-hash callbacks. This theorem is intentionally not a simp
rule. -/
theorem rootWith_publicHash_eq_rootM (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m] [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) :
    rootWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        sk pk = rootM vp core sk pk := rfl

/-- Callback-parametric arbitrary-depth recovery is the canonical explicit-query recovery after
instantiating the three public-hash callbacks. This theorem is intentionally not a simp rule. -/
theorem pkFromSigWith_publicHash_eq_pkFromSigM (vp : ValidatedParams)
    (core : CorePrimitives vp.params)
    {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sig : Signature vp core) (pk : core.PkSeed)
    (parts : DigestParts vp.params) :
    pkFromSigWith vp core (m := m) (PublicHash.f (m := m) core pk)
        (PublicHash.tl (m := m) core pk) (PublicHash.h (m := m) core pk)
        msg sig pk parts = pkFromSigM vp core msg sig pk parts := rfl

end GeneralHypertree

namespace HypertreeConformance

/-! ## Exact typed position trace -/

/-- Exact FIPS layer trajectory, indexed by the validated hypertree depth. -/
def trajectory (vp : ValidatedParams) (parts : DigestParts vp.params) :
    Vector (LayerPosition vp) vp.params.d :=
  Vector.ofFn (LayerPosition.atLayer vp parts)

/-- Observable layer/tree/leaf and address-layer/tree coordinates for one trajectory entry. -/
def traceEntry {vp : ValidatedParams} (pos : LayerPosition vp) : List ℕ :=
  [pos.layer.val, pos.tree.val, pos.leaf.val, pos.toAdrs.layer, pos.toAdrs.tree]

/-- Exact observable hypertree trajectory. -/
def trace (vp : ValidatedParams) (parts : DigestParts vp.params) :
    Vector (List ℕ) vp.params.d :=
  (trajectory vp parts).map traceEntry

@[simp]
theorem trajectory_get (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : Fin vp.params.d) :
    (trajectory vp parts).get j = LayerPosition.atLayer vp parts j := by
  change (Vector.ofFn (LayerPosition.atLayer vp parts))[j.val] = _
  exact Vector.getElem_ofFn j.isLt

@[simp]
theorem trace_get (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : Fin vp.params.d) :
    (trace vp parts).get j = traceEntry (LayerPosition.atLayer vp parts j) := by
  change ((Vector.ofFn (LayerPosition.atLayer vp parts)).map traceEntry)[j.val] = _
  rw [Vector.getElem_map, Vector.getElem_ofFn]

/-- The trace starts with the exact digest-derived tree and leaf. -/
theorem trace_zero (vp : ValidatedParams) (parts : DigestParts vp.params) :
    (trace vp parts).get ⟨0, vp.valid.d_pos⟩ =
      [0, parts.idxTree.val, parts.idxLeaf.val, 0, parts.idxTree.val] := by
  rw [trace_get, LayerPosition.atLayer_zero_eq_initial]
  rfl

/-- Every adjacent trace entry applies the FIPS low-bits/high-bits transition and propagates the
new layer/tree coordinates into the XMSS base address. -/
theorem trace_succ (vp : ValidatedParams) (parts : DigestParts vp.params)
    (j : Fin vp.params.d) (hnext : j.val + 1 < vp.params.d) :
    let current := LayerPosition.atLayer vp parts j
    (trace vp parts).get ⟨j.val + 1, hnext⟩ =
      [j.val + 1, current.tree.val / 2 ^ vp.params.hp,
        current.tree.val % 2 ^ vp.params.hp,
        j.val + 1, current.tree.val / 2 ^ vp.params.hp] := by
  rw [trace_get, LayerPosition.atLayer_succ_eq_next vp parts j hnext]
  simp [traceEntry]

end HypertreeConformance

end SLHDSA
