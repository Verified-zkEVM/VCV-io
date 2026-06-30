/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# Collision-Resistant Hash Functions

This file defines collision resistance for unkeyed hash functions and for
keyed hash function families, together with their security experiments.

## Collision Resistance

A function `f : X → Y` is collision-resistant if no efficient adversary can
find two distinct inputs `x ≠ x'` with `f x = f x'`.

## Keyed Hash Function Families

A keyed hash family samples a public key `k : K` and the adversary must find
a collision under `f k`. This is the form used in practical constructions and
in the Merkle-tree / FRI commitment-scheme setting where the hash key is a
protocol parameter.

## Main Definitions

- `CRAdversary X` — an adversary outputting a candidate collision pair.
- `crExp` — the collision-resistance experiment.
- `crAdvantage` — the advantage of a CR adversary.
- `KeyedHashFamily K X Y` — a keyed hash family.
- `KeyedCRAdversary K X` — an adversary for the keyed variant.
- `keyedCRExp` — the keyed collision-resistance experiment.
- `keyedCRAdvantage` — the advantage of a keyed CR adversary.
- `ROMHashSpec X Y` — adversary-facing random-oracle spec; carries no
  probability instances.
- `ROMHashSpec.cached X Y` — post-simulation companion; defeq to
  `ROMHashSpec X Y` but with the `IsUniformSpec` instance attached.
- `ROMHashSpec.cachingOracle` — `QueryImpl` bridge that consumes pre-spec
  queries and dispatches them through the generic `cachingOracle` on the
  cached spec. The spec transition happens only via `simulateQ`.
- `ROMCRAdversary X Y` — an adversary for the ROM variant.
- `romCRExp` — the ROM collision-resistance experiment.
- `romCRAdvantage` — the advantage of a ROM-CR adversary.
- `romCRAdvantage_le_birthday` — birthday bound on ROM-CR advantage.

## See also

- `VCVio/CryptoFoundations/CommitmentScheme.lean` — binding for commitment
  schemes; collision resistance of the underlying hash is the standard-model
  source of binding for hash-based commitments.
- `VCVio/OracleComp/QueryTracking/Collision.lean` — `CacheHasCollision`
  predicates and birthday bounds used to bound ROM-level collision probability.
-/


open OracleComp OracleSpec ENNReal

namespace CollisionResistance

variable {X Y : Type}

/-! ## Unkeyed Collision Resistance -/

/-- A collision-resistance adversary outputs a candidate pair of inputs
that it hopes form a collision under the target hash function. -/
def CRAdversary (X : Type) := ProbComp (X × X)

/-- Collision-resistance experiment: the adversary proposes a pair `(x, x')`,
and the experiment returns `true` iff the two inputs are distinct and map to
the same image under `f`. -/
def crExp [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (adversary : CRAdversary X) : ProbComp Bool := do
  let (x, x') ← adversary
  return decide (x ≠ x' ∧ f x = f x')

/-- Collision-resistance advantage: the probability that the adversary
produces a valid collision for `f`. -/
noncomputable def crAdvantage [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (adversary : CRAdversary X) : ℝ≥0∞ :=
  Pr[= true | crExp f adversary]

/-! ## Keyed Hash Function Families -/

variable {K : Type}

/-- A keyed hash family with key space `K`, domain `X`, and range `Y`.
The key-sampling algorithm is probabilistic; the hash itself is a
deterministic function of the key and input. -/
structure KeyedHashFamily (K X Y : Type) where
  keygen : ProbComp K
  hash : K → X → Y

/-- A keyed CR adversary receives the public key and outputs a candidate
collision pair. -/
def KeyedCRAdversary (K X : Type) := K → ProbComp (X × X)

/-- Keyed collision-resistance experiment: sample a key, run the adversary on
the key, and return `true` iff the adversary's pair is a valid collision
under `H.hash k`. -/
def keyedCRExp [DecidableEq X] [DecidableEq Y]
    (H : KeyedHashFamily K X Y) (adversary : KeyedCRAdversary K X) :
    ProbComp Bool := do
  let k ← H.keygen
  let (x, x') ← adversary k
  return decide (x ≠ x' ∧ H.hash k x = H.hash k x')

/-- Keyed collision-resistance advantage: the probability of producing a
valid collision under the sampled key. -/
noncomputable def keyedCRAdvantage [DecidableEq X] [DecidableEq Y]
    (H : KeyedHashFamily K X Y) (adversary : KeyedCRAdversary K X) : ℝ≥0∞ :=
  Pr[= true | keyedCRExp H adversary]

/-! ## ROM-Level Collision Resistance

Companion section modelling collision resistance directly in the random-oracle
model. A ROM-CR adversary is an oracle computation outputting a candidate
collision pair `(x, x')`, expressed in the adversary-facing `ROMHashSpec X Y`
which carries no probability instances. The experiment lifts the adversary
into the post-simulation companion `ROMHashSpec.cached X Y` (defeq, distinct
head symbol) where `IsUniformSpec` is in scope, then runs it inside
`cachingOracle` and queries the random oracle on both candidates sharing the
same cache; it wins iff `x ≠ x'` and the queried outputs coincide.

For any `t`-query ROM-CR adversary the advantage is bounded by the birthday
term `(t+2) * (t+1) / (2 * |Y|)` — a `(t+2)`-query game once the two
verification queries are accounted for.

Closes one of the layers requested in
[Verified-zkEVM/VCV-io#284](https://github.com/Verified-zkEVM/VCV-io/issues/284).
-/

/-- The random-oracle spec with domain `X` and range `Y`, as seen by the
adversary. Each input `x : X` is a distinct oracle index returning a value in
`Y`. This pre-cache spec carries no probability instances: a ROM-CR adversary
is a syntactic object, and probability semantics only attach to the
post-simulation spec `ROMHashSpec.cached` (defeq, distinct head symbol). -/
def ROMHashSpec (X Y : Type) : OracleSpec X := fun _ => Y

instance {X Y : Type} [DecidableEq X] [DecidableEq Y] :
    (ROMHashSpec X Y).DecidableEq where
  decidableEq_A := (inferInstanceAs (DecidableEq X))
  decidableEq_B := fun _ => (inferInstanceAs (DecidableEq Y))

/-- The post-simulation companion to `ROMHashSpec`: definitionally the same
`OracleSpec X`, but with a distinct head symbol so the `IsUniformSpec`
instance below is opted into only where probability reasoning is intended.
The adversary's pre-cache computation is converted into a post-cache
computation only via `simulateQ ROMHashSpec.cachingOracle`. -/
def ROMHashSpec.cached (X Y : Type) : OracleSpec X := fun _ => Y

instance {X Y : Type} [Fintype Y] : (ROMHashSpec.cached X Y).Fintype where
  fintype_B := fun _ => (inferInstanceAs (Fintype Y))

instance {X Y : Type} [Inhabited Y] : (ROMHashSpec.cached X Y).Inhabited where
  inhabited_B := fun _ => (inferInstanceAs (Inhabited Y))

instance {X Y : Type} [DecidableEq X] [DecidableEq Y] :
    (ROMHashSpec.cached X Y).DecidableEq where
  decidableEq_A := (inferInstanceAs (DecidableEq X))
  decidableEq_B := fun _ => (inferInstanceAs (DecidableEq Y))

noncomputable instance {X Y : Type} [Fintype Y] [Inhabited Y] :
    IsUniformSpec (ROMHashSpec.cached X Y) := IsUniformSpec.ofFintypeInhabited _

/-- Bridge caching oracle: a `QueryImpl` that takes adversary-facing
`ROMHashSpec X Y` queries and dispatches them through the generic
`cachingOracle` on the post-cache spec `ROMHashSpec.cached X Y`. The spec
transition from pre to cached happens only here, via `simulateQ`. -/
@[inline, reducible]
def ROMHashSpec.cachingOracle {X Y : Type} [DecidableEq X] :
    QueryImpl (ROMHashSpec X Y)
      (StateT (QueryCache (ROMHashSpec.cached X Y))
        (OracleComp (ROMHashSpec.cached X Y))) :=
  OracleSpec.cachingOracle (spec := ROMHashSpec.cached X Y)

/-- Specialised `simulateQ_query` lemma for the bridge: simulating a single
pre-spec query through `ROMHashSpec.cachingOracle` is the generic
`cachingOracle` action at the post-cache spec. The two specs are
definitionally equal as `OracleSpec X`, so this is `cachingOracle.simulateQ_query`
at the post-cache spec. -/
@[simp]
lemma ROMHashSpec.simulateQ_cachingOracle_query {X Y : Type} [DecidableEq X] (x : X) :
    simulateQ ROMHashSpec.cachingOracle (liftM ((ROMHashSpec X Y).query x)) =
      OracleSpec.cachingOracle (spec := ROMHashSpec.cached X Y) x :=
  cachingOracle.simulateQ_query x

/-- A ROM-CR adversary is an oracle computation outputting a candidate
collision pair under the random oracle. -/
def ROMCRAdversary (X Y : Type) : Type := OracleComp (ROMHashSpec X Y) (X × X)

/-- A ROM-CR adversary bundled with a total query bound. -/
structure BoundedROMCRAdversary (X Y : Type) (t : ℕ) where
  /-- The adversary's oracle computation. -/
  run : ROMCRAdversary X Y
  /-- The adversary makes at most `t` total queries. -/
  queryBound : IsTotalQueryBound run t

/-- ROM collision-resistance experiment: run the adversary inside the
`ROMHashSpec.cachingOracle` bridge from the empty cache, then query the
random oracle on both candidate inputs (verification queries share the
cache). Win iff the inputs are distinct and the queried outputs coincide.
The bridge takes the entire computation from `OracleComp (ROMHashSpec X Y)`
into `OracleComp (ROMHashSpec.cached X Y)` in one step — no separate
oracle-comp lift is needed. -/
def romCRExp [DecidableEq X] [DecidableEq Y]
    {t : ℕ} (A : BoundedROMCRAdversary X Y t) :
    OracleComp (ROMHashSpec.cached X Y)
      (Bool × QueryCache (ROMHashSpec.cached X Y)) :=
  (simulateQ ROMHashSpec.cachingOracle (do
    let (x, x') ← A.run
    let y ← (ROMHashSpec X Y).query x
    let y' ← (ROMHashSpec X Y).query x'
    return decide (x ≠ x' ∧ y = y'))).run ∅

/-- ROM collision-resistance advantage: probability that the adversary
produces a valid collision under the random oracle. -/
noncomputable def romCRAdvantage [DecidableEq X] [DecidableEq Y]
    [Fintype Y] [Inhabited Y]
    {t : ℕ} (A : BoundedROMCRAdversary X Y t) : ℝ≥0∞ :=
  Pr[fun z => z.1 = true | romCRExp A]

/-- The inner oracle computation of `romCRExp`, before `simulateQ`. Lives
entirely on the pre-cache spec — the spec transition happens at the
`simulateQ ROMHashSpec.cachingOracle` step. -/
private def romCRInner [DecidableEq X] [DecidableEq Y]
    {t : ℕ} (A : BoundedROMCRAdversary X Y t) :
    OracleComp (ROMHashSpec X Y) Bool := do
  let (x, x') ← A.run
  let y ← (ROMHashSpec X Y).query x
  let y' ← (ROMHashSpec X Y).query x'
  return decide (x ≠ x' ∧ y = y')

private lemma romCRExp_eq [DecidableEq X] [DecidableEq Y]
    {t : ℕ} (A : BoundedROMCRAdversary X Y t) :
    romCRExp A = (simulateQ ROMHashSpec.cachingOracle (romCRInner A)).run ∅ := rfl

/-- The total query bound on `romCRInner` is `t + 2` — `t` from the adversary
plus the two verification queries. -/
private lemma romCRInner_totalBound [DecidableEq X] [DecidableEq Y]
    {t : ℕ} (A : BoundedROMCRAdversary X Y t) :
    IsTotalQueryBound (romCRInner A) (t + 2) := by
  refine isTotalQueryBound_bind A.queryBound fun ⟨_x, _x'⟩ => ?_
  simp only [isTotalQueryBound_query_bind_iff]
  exact ⟨by lia, fun _y => ⟨Nat.one_pos, fun _ => trivial⟩⟩

/-- A win in the ROM-CR experiment implies a collision in the final cache:
the verification queries cache `x ↦ y` and `x' ↦ y'` with `x ≠ x'` and
`y = y'`, which is exactly `CacheHasCollision`. -/
private lemma romCRWin_implies_collision [DecidableEq X] [DecidableEq Y] [Finite Y] [Inhabited Y]
    {t : ℕ} (A : BoundedROMCRAdversary X Y t) :
    ∀ z ∈ support ((simulateQ ROMHashSpec.cachingOracle (romCRInner A)).run ∅),
      z.1 = true → CacheHasCollision z.2 := by
  intro z hz hwin
  simp only [romCRInner, simulateQ_bind, simulateQ_pure, StateT.run_bind, support_bind,
    Set.mem_iUnion, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨⟨x, x'⟩, cache₁⟩, _hmem₁,
    ⟨y, cache₂⟩, hmem₂, ⟨y', cache₃⟩, hmem₃, hz⟩ := hz
  rw [hz] at hwin ⊢
  simp only [decide_eq_true_eq] at hwin
  obtain ⟨hne, hyy⟩ := hwin
  rw [ROMHashSpec.simulateQ_cachingOracle_query] at hmem₂ hmem₃
  exact ⟨x, x', y, y', hne,
    QueryImpl.withCaching_cache_le _ x' cache₂ (y', cache₃) hmem₃
      (cachingOracle_query_caches x cache₁ y cache₂ hmem₂),
    cachingOracle_query_caches x' cache₂ y' cache₃ hmem₃, heq_of_eq hyy⟩

/-- **ROM Collision Resistance birthday bound**: for any `t`-query ROM-CR
adversary `A` over a hash range `Y`, the advantage is bounded by
`(t+2) * (t+1) / (2 * |Y|)` (a vacuous bound when `|Y| = 0`). The two extra
queries account for the experiment's verification queries, which share the
adversary's cache. -/
theorem romCRAdvantage_le_birthday [DecidableEq X] [DecidableEq Y] [Fintype Y] [Inhabited X]
    [Inhabited Y] {t : ℕ} (A : BoundedROMCRAdversary X Y t) :
    romCRAdvantage A ≤ (((t + 2) * (t + 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card Y) := by
  simp only [romCRAdvantage, romCRExp_eq]
  exact (probEvent_mono (romCRWin_implies_collision A)).trans <|
    probEvent_cacheCollision_le_birthday_total_tight (spec := ROMHashSpec.cached X Y)
      (romCRInner A) (t + 2) (romCRInner_totalBound A) fun _ => le_rfl

end CollisionResistance
