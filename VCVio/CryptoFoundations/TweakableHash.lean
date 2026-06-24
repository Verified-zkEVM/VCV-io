/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Tweakable Hash Families

A tweakable hash family `Th : PkSeed → Tweak → M → Y` generalizes `KeyedHashFamily` by
splitting the key into a *sampled* public seed and a *caller-supplied* abstract tweak. It is the
abstraction that the SLH-DSA / SPHINCS+ functions `F`, `H`, and `T_ℓ` instantiate (with the
tweak being the 32-byte address `ADRS`), and against which their multi-target security notions
(`VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget`) are stated.

This file provides the data abstraction only; the security games live in `MultiTarget` and are
deliberately stated over plain functions `X → Y` / `Tweak → M → Y`, so a partially-applied
tweakable hash can be fed in without a circular dependency.

With `Tweak := Unit` this is definitionally a keyed hash family
(`seedGen : ProbComp PkSeed`, `eval : PkSeed → M → Y`), so nothing is lost relative to the
existing `KeyedHashFamily` surface.
-/


open OracleComp

/-- A tweakable hash family: a sampled public seed plus a deterministic evaluation taking a
public seed, a tweak, and a message to a digest. -/
structure TweakableHash (PkSeed Tweak M Y : Type) where
  /-- Sample the public seed `PK.seed`. -/
  seedGen : ProbComp PkSeed
  /-- Evaluate the tweakable hash at a public seed, tweak, and message. -/
  eval : PkSeed → Tweak → M → Y

namespace TweakableHash

variable {PkSeed Tweak Y : Type}

/-- The two-input node hash `(left ‖ right) ↦ digest` at a fixed seed and tweak, as used to
combine sibling nodes in a Merkle tree. -/
def nodeHash (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed) (t : Tweak)
    (l r : Y) : Y :=
  th.eval pk t (l, r)

end TweakableHash
