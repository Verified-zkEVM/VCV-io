/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Tweakable Hash Families

A tweakable hash family `Th : PkSeed → Tweak → M → Y` generalizes `KeyedHashFamily` by
splitting the key into a *sampled* public seed and a *caller-supplied* abstract tweak. It is the
abstraction that the SLH-DSA / SPHINCS+ functions `F`, `H`, and `T_ℓ` instantiate (with the tweak
being the canonical encoded `ADRS` key), and against which their multi-target security notions
(`TweakableHash.SM_DT_TCR_Advantage`, `TweakableHash.SM_DT_PRE_Advantage`) are stated.

This file provides the data abstraction only; the security games live under
`HardnessAssumptions/TweakableHash/`. They take a `TweakableHash` whole rather than a
partially-applied function, because `seedGen` is what samples the public parameter that the game
must withhold from the adversary during target selection.

With `Tweak := Unit` this is definitionally a keyed hash family
(`seedGen : ProbComp PkSeed`, `eval : PkSeed → M → Y`), so nothing is lost relative to the
existing `KeyedHashFamily` surface.

## Collections

`TweakableHashCollection` is a family of tweakable hashes sharing one public seed and one tweak
space, differing only in their message types — SLH-DSA's `F`, `H` and `T_ℓ` under one `PK.seed` and
one `ADRS` space. It carries no `seedGen` of its own: a game samples one seed, from the attacked
member's `TweakableHash.seedGen`, and hands it to every member.

Indexing is by an explicit `ι`. HK22 and BDHMS both key a collection member by the *length* of the
queried message, which cannot name two members of equal message length; `ι` can.

The security notions under `HardnessAssumptions/TweakableHash/` take the attacked member and the
collection as separate parameters, as BDHMS's `Game^{SM-DT-TCR-C}_{A,THF,THF_C,t}` does, so whether
the attacked member is itself in the collection is fixed at instantiation:

- `empty` gives the stand-alone notion, where the collection oracle is unqueryable. This is DKKW
  Def. 3, whose adversary has the challenge oracle and nothing else.
- `cons th thColl` puts the attacked member in its own collection at index `none`, which is HK22's
  `Th_m ∈ Th_λ`. HK22 motivates it explicitly: a challenge query may depend on the output of
  another member of the collection, "or even the same function but with different tweaks".
-/

@[expose] public section

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

/-! ## Collections of tweakable hashes -/

/-- A collection of tweakable hashes indexed by `ι`, sharing one public seed, one tweak space and
one digest space, and differing only in their message types. This is the shape of SLH-DSA's `F`, `H`
and `T_ℓ` under a single `PK.seed` and a single `ADRS` space.

There is deliberately no `seedGen` field. A security game samples exactly one seed — from the
`TweakableHash.seedGen` of the member under attack — and evaluates every member at it. A collection
carrying its own sampler would let a game measure the attacked member and the simulated members at
two independent seeds. -/
structure TweakableHashCollection (ι PkSeed Tweak Y : Type) where
  /-- The message type of the member at index `i`. -/
  Msg : ι → Type
  /-- Evaluate the member at index `i` on a public seed, tweak, and message. -/
  eval : (i : ι) → PkSeed → Tweak → Msg i → Y

namespace TweakableHashCollection

/-- The empty collection, indexed by `Empty`. A game instantiated at this collection has a
collection oracle whose query type is uninhabited, hence unqueryable, which is exactly the
stand-alone form of the notion. -/
def empty (PkSeed Tweak Y : Type) : TweakableHashCollection Empty PkSeed Tweak Y where
  Msg i := i.elim
  eval i := i.elim

/-- `thColl` extended with `th` at index `none`.

This is how a game instantiation places its *attacked* member inside its own collection, which is
what HK22's `Th_m ∈ Th_λ` asks for. The point is not bookkeeping: with the seed withheld during
target selection, the challenge oracle evaluates the attacked member only at target tweaks and
under the target cap, so without this the attacked member cannot be evaluated at a tweak that is
not a target — and a reduction may need to do exactly that.

Membership is definitional rather than a hypothesis: `cons_eval_none` is `rfl`. -/
def cons {ι PkSeed Tweak M Y : Type} (th : TweakableHash PkSeed Tweak M Y)
    (thColl : TweakableHashCollection ι PkSeed Tweak Y) :
    TweakableHashCollection (Option ι) PkSeed Tweak Y where
  Msg := fun | none => M | some i => thColl.Msg i
  eval := fun | none => th.eval | some i => thColl.eval i

variable {ι PkSeed Tweak M Y : Type} {th : TweakableHash PkSeed Tweak M Y}
  {thColl : TweakableHashCollection ι PkSeed Tweak Y}

@[simp] theorem cons_eval_none : (cons th thColl).eval none = th.eval := rfl

@[simp] theorem cons_eval_some (i : ι) : (cons th thColl).eval (some i) = thColl.eval i := rfl

/-- Deliberately not `@[simp]`: `Msg` occurs inside the query type of the collection oracle's
`OracleSpec`, so rewriting it under a `simulateQ` strands the goal in a form the query lemmas can
no longer match. -/
theorem cons_Msg_none : (cons th thColl).Msg none = M := rfl

/-- Not `@[simp]`, for the reason given on `cons_Msg_none`. -/
theorem cons_Msg_some (i : ι) : (cons th thColl).Msg (some i) = thColl.Msg i := rfl

end TweakableHashCollection
