/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.StateSeparating.Hybrid
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# State-Separating Proofs: ElGamal IND-CPA via DDH

A handler-level formulation of the many-query *left-or-right* IND-CPA game for
ElGamal in the state-separating style.
The example wraps the ElGamal / DDH machinery from `Examples.ElGamal.Basic` and
`VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman` into the
`QueryImpl.Stateful` API, illustrating how `link`, `advantage`, and
`shiftLeft` organize a security proof.

The game defined here is strictly stronger than the one-time IND-CPA game proved secure in
`Examples/ElGamal/Basic.lean`: the adversary may make an unbounded number of `LR` and `GETPK`
queries under a single shared key. The many-query game implies the one-time game by a
standard `q`-way hybrid over the `LR` queries.

## Oracle interfaces

For a fixed generator `gen : G`, both the LR challenge and the underlying DDH game export a
two-oracle interface:

* `lrSpec G = (Unit →ₒ G) + ((G × G) →ₒ (G × G))`
  * `GETPK : Unit →ₒ G` returns the challenger's public key, allowing the adversary to choose
    challenge messages as a function of `pk`.
  * `LR : (G × G) →ₒ (G × G)` takes a pair of messages `(m₀, m₁)` and returns an
    ElGamal-shaped ciphertext under the challenger's secret bit.
* `dhSpec G = (Unit →ₒ G) + (Unit →ₒ (G × G))`
  * `GETPK : Unit →ₒ G` returns `a • gen` for the (lazily sampled) DDH first exponent `a`.
  * `DHCHALLENGE : Unit →ₒ (G × G)` returns `(b • gen, T)` for fresh `b`, where `T = (a*b) •
    gen` (real) or `T = c • gen` for fresh `c` (random).

This two-oracle DDH interface is the multi-query / shared-`a` version of the standard DDH
distribution: the single secret exponent `a` is shared across all `GETPK` and `DHCHALLENGE`
answers. The multi-query DDH assumption (`dhTripleReal` and `dhTripleRand` are
computationally indistinguishable) is the cryptographic primitive the headline bound reduces
to; the standard multi-to-single-query hybrid (which bounds this multi-query gap by `q` times
the single-query DDH advantage) is orthogonal to the state-separating argument presented here.

## Game handlers

* `elgamalLR_left F gen` and `elgamalLR_right F gen` are the two LR-style games. The secret
  key `sk` is *lazily sampled* on the first `GETPK` or `LR` query and cached in the handler
  state `Option F` so that all subsequent queries share the same `sk`. Each `LR` query samples
  fresh randomness `r`, producing independent encryptions under the shared key.
* `dhTripleReal F gen` and `dhTripleRand F gen` are the corresponding "real" and "random" DDH
  handlers. They cache the secret exponent `a` lazily (state `Option F`) and sample fresh
  per-query exponents `b` (and `c` in the random case). Each `GETPK` answer thus uses a
  consistent `pk = a • gen` across queries, while each `DHCHALLENGE` uses fresh `b`.

## Reduction handlers

* `dhToLR_leftHandler` and `dhToLR_rightHandler` are stateless reduction handlers. Each LR
  query is forwarded to the corresponding DDH oracle, then projected: `GETPK` is forwarded
  unchanged, while `LR (m₀, m₁)` maps `DHCHALLENGE`'s `(B, T)` to the ciphertext `(B, T + m_b)`
  for `m_b ∈ {m₀, m₁}`.
* `dhToLR_left` and `dhToLR_right` are the corresponding `QueryImpl.Stateful`s built via
  `QueryImpl.Stateful.ofStateless`.

## state-separating-style hybrid bound

The classical 5-game / 4-hop hybrid

```
elgamalLR_left  ↔  dhToLR_left.link dhTripleReal
                ≈  dhToLR_left.link dhTripleRand   -- multi-query DDH gap
                ↔  dhToLR_right.link dhTripleRand  -- rand-swap symmetry (uniform masking)
                ≈  dhToLR_right.link dhTripleReal  -- multi-query DDH gap
                ↔  elgamalLR_right
```

collapses through `QueryImpl.Stateful.advantage_triangle` and
`QueryImpl.Stateful.advantage_link_left_eq_advantage_shiftLeft` into the bound on `elgamalLR_left`
versus `elgamalLR_right`. The three program-equivalence hops (1, 3, 5) are discharged as
`evalDist_runProb_*` lemmas below. The two remaining gaps (2, 4) are exactly the multi-query
DDH advantages of the shifted reduction adversaries `dhToLR_{left,right}.shiftLeft A`; they
appear on the right-hand side of the final bound `elgamalLR_left_advantage_right_le`.
-/

open OracleSpec OracleComp ProbComp

namespace VCVio.StateSeparating.Examples.ElGamal

/-! ### Oracle interfaces -/

/-- The LR oracle interface for IND-CPA: `GETPK : Unit →ₒ G` returns the challenger's public
key, and `LR : (G × G) →ₒ (G × G)` takes a pair of messages and returns a challenge ciphertext
under the secret bit. The adversary may interleave calls to both oracles in any order. -/
@[reducible] def lrSpec (G : Type) : OracleSpec (Unit ⊕ (G × G)) :=
  (Unit →ₒ G) + ((G × G) →ₒ (G × G))

/-- The DDH oracle interface (multi-query / shared-`a` variant): `GETPK : Unit →ₒ G` returns
`a • gen`, and `DHCHALLENGE : Unit →ₒ (G × G)` returns `(b • gen, T)` for fresh `b`. -/
@[reducible] def dhSpec (G : Type) : OracleSpec (Unit ⊕ Unit) :=
  (Unit →ₒ G) + (Unit →ₒ (G × G))

variable {F : Type} [CommRing F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-! ### DDH triple handlers -/

/-- The "real" DDH handler (multi-query, shared-`a`).

The first exponent `a` is lazily sampled on first access and cached in the state. `GETPK`
returns `a • gen` and `DHCHALLENGE` returns `(b • gen, (a * b) • gen)` for fresh `b`. -/
noncomputable def dhTripleReal (gen : G) :
    QueryImpl.Stateful unifSpec (dhSpec G) (Option F)
  | Sum.inl _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F)
            pure (a • gen, some a)
        | some a => pure (a • gen, some a)
    | Sum.inr _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F)
            let b ← ($ᵗ F)
            pure ((b • gen, (a * b) • gen), some a)
        | some a => do
            let b ← ($ᵗ F)
            pure ((b • gen, (a * b) • gen), some a)

/-- The "random" DDH handler (multi-query, shared-`a`). Identical to `dhTripleReal` except
`DHCHALLENGE` returns `(b • gen, c • gen)` for fresh `b, c`. -/
noncomputable def dhTripleRand (gen : G) :
    QueryImpl.Stateful unifSpec (dhSpec G) (Option F)
  | Sum.inl _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F)
            pure (a • gen, some a)
        | some a => pure (a • gen, some a)
    | Sum.inr _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F)
            let b ← ($ᵗ F)
            let c ← ($ᵗ F)
            pure ((b • gen, c • gen), some a)
        | some a => do
            let b ← ($ᵗ F)
            let c ← ($ᵗ F)
            pure ((b • gen, c • gen), some a)

/-! ### ElGamal LR-style games -/

/-- The "left-message" ElGamal LR game.

* `GETPK` returns `sk • gen`, lazily sampling `sk` if necessary.
* `LR (m₀, _)` returns `(r • gen, (sk * r) • gen + m₀)` for fresh randomness `r`, lazily
  sampling `sk` if necessary.

The convention `(B, T + m_b)` (rather than `(B, m_b + T)`) matches the DDH-to-LR reduction's
output, so the equivalence with `dhToLR_left.link dhTripleReal` is definitional up to
alpha-renaming of the sampled exponents (`a, b` on the DDH side and `sk, r` here). -/
noncomputable def elgamalLR_left (gen : G) :
    QueryImpl.Stateful unifSpec (lrSpec G) (Option F)
  | Sum.inl _ => fun st => match st with
        | none => do
            let sk ← ($ᵗ F)
            pure (sk • gen, some sk)
        | some sk => pure (sk • gen, some sk)
    | Sum.inr (m₀, _) => fun st => match st with
        | none => do
            let sk ← ($ᵗ F)
            let r ← ($ᵗ F)
            pure ((r • gen, (sk * r) • gen + m₀), some sk)
        | some sk => do
            let r ← ($ᵗ F)
            pure ((r • gen, (sk * r) • gen + m₀), some sk)

/-- The "right-message" ElGamal LR game. Same as `elgamalLR_left` except `LR (_, m₁)` returns
`(r • gen, (sk * r) • gen + m₁)`. -/
noncomputable def elgamalLR_right (gen : G) :
    QueryImpl.Stateful unifSpec (lrSpec G) (Option F)
  | Sum.inl _ => fun st => match st with
        | none => do
            let sk ← ($ᵗ F)
            pure (sk • gen, some sk)
        | some sk => pure (sk • gen, some sk)
    | Sum.inr (_, m₁) => fun st => match st with
        | none => do
            let sk ← ($ᵗ F)
            let r ← ($ᵗ F)
            pure ((r • gen, (sk * r) • gen + m₁), some sk)
        | some sk => do
            let r ← ($ᵗ F)
            pure ((r • gen, (sk * r) • gen + m₁), some sk)

/-! ### DDH-to-LR reductions -/

/-- Stateless reduction handler encrypting the *left* message. Forwards `GETPK` on `lr`
to `GETPK` on `dh`, and forwards `LR (m₀, _)` to `DHCHALLENGE` on `dh`, returning the pair
`(B, T + m₀)` from the DDH challenge `(B, T)`. -/
def dhToLR_leftHandler {G : Type} [Add G] :
    QueryImpl (lrSpec G) (OracleComp (dhSpec G))
  | Sum.inl _ => ((dhSpec G).query (Sum.inl ()) : OracleComp (dhSpec G) G)
  | Sum.inr (m₀, _) => do
      let bt ← ((dhSpec G).query (Sum.inr ()) : OracleComp (dhSpec G) (G × G))
      pure (bt.1, bt.2 + m₀)

/-- Stateless reduction handler encrypting the *right* message. -/
def dhToLR_rightHandler {G : Type} [Add G] :
    QueryImpl (lrSpec G) (OracleComp (dhSpec G))
  | Sum.inl _ => ((dhSpec G).query (Sum.inl ()) : OracleComp (dhSpec G) G)
  | Sum.inr (_, m₁) => do
      let bt ← ((dhSpec G).query (Sum.inr ()) : OracleComp (dhSpec G) (G × G))
      pure (bt.1, bt.2 + m₁)

/-- DDH-to-LR reduction encrypting the left message as a stateless handler. -/
def dhToLR_left {G : Type} [Add G] : QueryImpl.Stateful (dhSpec G) (lrSpec G) PUnit :=
  QueryImpl.Stateful.ofStateless dhToLR_leftHandler

/-- DDH-to-LR reduction encrypting the right message as a stateless handler. -/
def dhToLR_right {G : Type} [Add G] : QueryImpl.Stateful (dhSpec G) (lrSpec G) PUnit :=
  QueryImpl.Stateful.ofStateless dhToLR_rightHandler

/-! ### Reduction equivalences (Hops #1 and #5)

Each of the two named lemmas below shows that two state-separating handlers
produce the same distribution against any adversary `A`.
They are the state-separating-level analogues of the rewrites in
`Examples.ElGamal.Basic.IND_CPA_OneTime_game_evalDist_eq_ddhExpReal`. -/

section ReductionEquivalences

/-- Per-(query, state) handler equivalence (under `evalDist`) between the composed
"reduction ∘ dhTripleReal" and the ElGamal LR-left game.

The `Sum.inl` (GETPK) cases are immediate: both sides return `(sk • gen, some sk)` after
sampling `sk` from `$ᵗ F`. The `Sum.inr` (LR) cases reduce to the same `do let sk; let r; pure
((r • gen, (sk * r) • gen + m₀), some sk)` form on both sides after pushing the reduction's
final `pure (B, T + m₀)` map through the bind. -/
private theorem composed_real_left_handler_evalDist (gen : G)
    (q : Unit ⊕ (G × G)) (s : Option F) :
    𝒟[(simulateQ (dhTripleReal (F := F) gen)
          ((dhToLR_leftHandler (G := G)) q)).run s] =
      𝒟[((elgamalLR_left (F := F) gen) q).run s] := by
  rcases q with ⟨⟩ | ⟨m₀, _⟩
  · cases s with
    | none =>
        simp [dhToLR_leftHandler, dhTripleReal, elgamalLR_left,
          simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]
    | some sk =>
        simp [dhToLR_leftHandler, dhTripleReal, elgamalLR_left,
          simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]
  · cases s with
    | none =>
        simp only [dhToLR_leftHandler, dhTripleReal, elgamalLR_left,
          simulateQ_map, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, StateT.run_map, bind_pure_comp]
        dsimp only [StateT.run]
        simp only [map_bind, Functor.map_map]
    | some sk =>
        simp only [dhToLR_leftHandler, dhTripleReal, elgamalLR_left,
          simulateQ_map, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, StateT.run_map, bind_pure_comp]
        dsimp only [StateT.run]
        simp only [Functor.map_map]

/-- Per-(query, state) handler equivalence (under `evalDist`) between the composed
"reduction ∘ dhTripleReal" and the ElGamal LR-right game. -/
private theorem composed_real_right_handler_evalDist (gen : G)
    (q : Unit ⊕ (G × G)) (s : Option F) :
    𝒟[(simulateQ (dhTripleReal (F := F) gen)
          ((dhToLR_rightHandler (G := G)) q)).run s] =
      𝒟[((elgamalLR_right (F := F) gen) q).run s] := by
  rcases q with ⟨⟩ | ⟨_, m₁⟩
  · cases s with
    | none =>
        simp [dhToLR_rightHandler, dhTripleReal, elgamalLR_right,
          simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]
    | some sk =>
        simp [dhToLR_rightHandler, dhTripleReal, elgamalLR_right,
          simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]
  · cases s with
    | none =>
        simp only [dhToLR_rightHandler, dhTripleReal, elgamalLR_right,
          simulateQ_map, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, StateT.run_map, bind_pure_comp]
        dsimp only [StateT.run]
        simp only [map_bind, Functor.map_map]
    | some sk =>
        simp only [dhToLR_rightHandler, dhTripleReal, elgamalLR_right,
          simulateQ_map, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, StateT.run_map, bind_pure_comp]
        dsimp only [StateT.run]
        simp only [Functor.map_map]

/-- Hop #1: linking the DDH-real handler under the *left*-message reduction
produces the same output distribution as the LR-left game itself. -/
theorem evalDist_runProb_dhToLR_left_link_real_eq_elgamalLR_left
    (gen : G) {α : Type} (A : OracleComp (lrSpec G) α) :
    𝒟[(dhToLR_left.link (dhTripleReal (F := F) gen)).runProb
        (PUnit.unit, none) A] =
      𝒟[(elgamalLR_left (F := F) gen).runProb none A] := by
  unfold QueryImpl.Stateful.runProb
  rw [show dhToLR_left = QueryImpl.Stateful.ofStateless (dhToLR_leftHandler (G := G)) from rfl,
    QueryImpl.Stateful.run_link_left_ofStateless]
  unfold QueryImpl.Stateful.run
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  exact QueryImpl.Stateful.simulateQ_StateT_evalDist_congr
    (composed_real_left_handler_evalDist (F := F) gen) A none

/-- Hop #5: the right-message analogue of
`evalDist_runProb_dhToLR_left_link_real_eq_elgamalLR_left`. -/
theorem evalDist_runProb_dhToLR_right_link_real_eq_elgamalLR_right
    (gen : G) {α : Type} (A : OracleComp (lrSpec G) α) :
    𝒟[(dhToLR_right.link (dhTripleReal (F := F) gen)).runProb
        (PUnit.unit, none) A] =
      𝒟[(elgamalLR_right (F := F) gen).runProb none A] := by
  unfold QueryImpl.Stateful.runProb
  rw [show dhToLR_right = QueryImpl.Stateful.ofStateless (dhToLR_rightHandler (G := G)) from rfl,
    QueryImpl.Stateful.run_link_left_ofStateless]
  unfold QueryImpl.Stateful.run
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  exact QueryImpl.Stateful.simulateQ_StateT_evalDist_congr
    (composed_real_right_handler_evalDist (F := F) gen) A none

end ReductionEquivalences

/-! ### Rand-swap symmetry (Hop #3)

Under `dhTripleRand`, the DDH-challenge oracle returns a fresh, uniform third component
`c • gen`; assuming `(· • gen) : F → G` is bijective, this third component is a uniform
element of `G` and acts as a one-time pad additively masking `m₀` or `m₁`. Pointwise,
`(b • gen, c • gen + m₀)` and `(b • gen, c • gen + m₁)` therefore have the same distribution.

This is the state-separating analogue of
`Examples.ElGamal.Basic.IND_CPA_OneTime_DDHReduction_rand_half`: a handler-level
uniform-masking argument lifted across the whole adversary via
`simulateQ_StateT_evalDist_congr`. -/

section RandSwapSymmetry

variable [Finite F] [SampleableType G]

/-- Per-(query, state) handler equivalence (under `evalDist`) between the composed
"left reduction ∘ dhTripleRand" and "right reduction ∘ dhTripleRand". `GETPK` cases are
identical on both sides; the `LR` case reduces to the uniform-masking argument (`c • gen + m₀`
and `c • gen + m₁` have the same distribution over `c ← $ᵗ F` when `(· • gen)` is bijective)
after pushing the reductions' post-processing `pure (B, T + m_b)` through the bind. -/
private theorem composed_rand_swap_handler_evalDist (gen : G)
    (hg : Function.Bijective (fun x : F => x • gen))
    (q : Unit ⊕ (G × G)) (s : Option F) :
    𝒟[(simulateQ (dhTripleRand (F := F) gen)
          ((dhToLR_leftHandler (G := G)) q)).run s] =
      𝒟[(simulateQ (dhTripleRand (F := F) gen)
          ((dhToLR_rightHandler (G := G)) q)).run s] := by
  rcases q with ⟨⟩ | ⟨m₀, m₁⟩
  · -- GETPK: both sides are the same `simulateQ` applied to the identical
    -- `query (Sum.inl ())`, hence definitionally equal.
    rfl
  · -- LR (m₀, m₁): normalise both sides to bind form and apply the uniform-masking lemma.
    -- The `step` helper shows that for any offset `m`, the composed handler reduces to a
    -- concrete `do b; c; pure ((b•gen, c•gen + m), some _)` ProbComp (modulo the state `s`).
    have step : ∀ (m : G),
        𝒟[(simulateQ (dhTripleRand (F := F) gen)
              ((dhToLR_leftHandler (G := G)) (Sum.inr (m, m)))).run s] =
          𝒟[do
              let bt ← (((dhTripleRand (F := F) gen) (Sum.inr ())).run s
                : ProbComp ((G × G) × Option F))
              pure ((bt.1.1, bt.1.2 + m), bt.2)] := by
      intro m
      simp only [dhToLR_leftHandler, simulateQ_query_bind, simulateQ_pure,
        OracleQuery.input_query, StateT.run_bind, monadLift_self, StateT.run_pure]
      rfl
    -- `dhToLR_leftHandler (Sum.inr (m₀, m₁))` only depends on `m₀`, and `dhToLR_rightHandler
    -- (Sum.inr (m₀, m₁))` only depends on `m₁`. Re-express both handler applications via
    -- the unified `step` helper.
    have left_eq :
        𝒟[(simulateQ (dhTripleRand (F := F) gen)
            ((dhToLR_leftHandler (G := G)) (Sum.inr (m₀, m₁)))).run s] =
          𝒟[(simulateQ (dhTripleRand (F := F) gen)
            ((dhToLR_leftHandler (G := G)) (Sum.inr (m₀, m₀)))).run s] := rfl
    have right_eq :
        𝒟[(simulateQ (dhTripleRand (F := F) gen)
            ((dhToLR_rightHandler (G := G)) (Sum.inr (m₀, m₁)))).run s] =
          𝒟[(simulateQ (dhTripleRand (F := F) gen)
            ((dhToLR_leftHandler (G := G)) (Sum.inr (m₁, m₁)))).run s] := rfl
    rw [left_eq, right_eq, step m₀, step m₁]
    -- Now the goal depends only on `((dhTripleRand gen) (Sum.inr ())).run s`, which
    -- unfolds to a concrete ProbComp. Case-split on `s` and apply the uniform-masking lemma.
    cases s with
    | none =>
        simp only [dhTripleRand, StateT.run, monad_norm]
        change 𝒟[do
              let a ← ($ᵗ F)
              let b ← ($ᵗ F)
              let c ← ($ᵗ F)
              pure ((b • gen, c • gen + m₀), some a)] =
          𝒟[do
              let a ← ($ᵗ F)
              let b ← ($ᵗ F)
              let c ← ($ᵗ F)
              pure ((b • gen, c • gen + m₁), some a)]
        rw [evalDist_bind]
        conv_rhs => rw [evalDist_bind]
        refine bind_congr fun a => ?_
        rw [evalDist_bind]
        conv_rhs => rw [evalDist_bind]
        refine bind_congr fun b => ?_
        exact evalDist_bind_bijective_add_right_eq
          (α := F) (β := G) (fun x : F => x • gen) hg m₀ m₁
          (fun y => pure ((b • gen, y), some a))
    | some a =>
        simp only [dhTripleRand, StateT.run, monad_norm]
        change 𝒟[do
              let b ← ($ᵗ F)
              let c ← ($ᵗ F)
              pure ((b • gen, c • gen + m₀), some a)] =
          𝒟[do
              let b ← ($ᵗ F)
              let c ← ($ᵗ F)
              pure ((b • gen, c • gen + m₁), some a)]
        rw [evalDist_bind]
        conv_rhs => rw [evalDist_bind]
        refine bind_congr fun b => ?_
        exact evalDist_bind_bijective_add_right_eq
          (α := F) (β := G) (fun x : F => x • gen) hg m₀ m₁
          (fun y => pure ((b • gen, y), some a))

/-- Hop #3: under the DDH-random handler, the left- and right-message reductions produce the
same output distribution against any adversary. The proof lifts the per-query uniform-masking
argument `evalDist_bind_bijective_add_right_eq` across the full adversary via
`simulateQ_StateT_evalDist_congr`. -/
theorem evalDist_runProb_dhToLR_link_rand_swap
    (gen : G) (hg : Function.Bijective (fun x : F => x • gen))
    {α : Type} (A : OracleComp (lrSpec G) α) :
    𝒟[(dhToLR_left.link (dhTripleRand (F := F) gen)).runProb
        (PUnit.unit, none) A] =
      𝒟[(dhToLR_right.link (dhTripleRand (F := F) gen)).runProb
        (PUnit.unit, none) A] := by
  unfold QueryImpl.Stateful.runProb
  rw [show dhToLR_left = QueryImpl.Stateful.ofStateless (dhToLR_leftHandler (G := G)) from rfl,
    show dhToLR_right = QueryImpl.Stateful.ofStateless (dhToLR_rightHandler (G := G)) from rfl,
    QueryImpl.Stateful.run_link_left_ofStateless, QueryImpl.Stateful.run_link_left_ofStateless]
  unfold QueryImpl.Stateful.run
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  exact QueryImpl.Stateful.simulateQ_StateT_evalDist_congr
    (composed_rand_swap_handler_evalDist (F := F) gen hg) A none

end RandSwapSymmetry

/-! ### End-to-end advantage bound

The headline security statement: the many-query LR-IND-CPA advantage of ElGamal is bounded by
the sum of two multi-query DDH advantages (one for each message slot). The multi-query DDH
advantage is the standard cryptographic hardness assumption in this model; reducing it further
to the single-query `DiffieHellman.ddhGuessAdvantage` is a separate hybrid argument orthogonal
to the state-separating reasoning here. -/

/-- The advantage of distinguishing `elgamalLR_left gen` from `elgamalLR_right gen` is bounded
by the sum of two multi-query DDH advantages, one against the shifted left-message reduction
adversary and one against the shifted right-message reduction adversary. -/
theorem elgamalLR_left_advantage_right_le
    [Finite F] [SampleableType G]
    (gen : G) (hg : Function.Bijective (fun x : F => x • gen))
    (A : OracleComp (lrSpec G) Bool) :
    (elgamalLR_left (F := F) gen).advantage none
        (elgamalLR_right (F := F) gen) none A ≤
      (dhTripleReal (F := F) gen).advantage none (dhTripleRand (F := F) gen) none
          (dhToLR_left.shiftLeft PUnit.unit A)
      + (dhTripleReal (F := F) gen).advantage none (dhTripleRand (F := F) gen) none
          (dhToLR_right.shiftLeft PUnit.unit A) := by
  set G₁ := dhToLR_left.link (dhTripleReal (F := F) gen) with hG₁
  set G₂ := dhToLR_left.link (dhTripleRand (F := F) gen) with hG₂
  set G₃ := dhToLR_right.link (dhTripleRand (F := F) gen) with hG₃
  set G₄ := dhToLR_right.link (dhTripleReal (F := F) gen) with hG₄
  -- Hop #1: (elgamalLR_left).advantage G₁ A = 0
  have h1 : (elgamalLR_left (F := F) gen).advantage none G₁ (PUnit.unit, none) A = 0 := by
    rw [hG₁, QueryImpl.Stateful.advantage_eq_of_evalDist_runProb_eq_right
      (evalDist_runProb_dhToLR_left_link_real_eq_elgamalLR_left (F := F) gen A)]
    exact QueryImpl.Stateful.advantage_self _ _ _
  -- Hop #3: G₂.advantage G₃ A = 0
  have h3 : G₂.advantage (PUnit.unit, none) G₃ (PUnit.unit, none) A = 0 := by
    rw [hG₂, hG₃, QueryImpl.Stateful.advantage_eq_of_evalDist_runProb_eq_right
      (evalDist_runProb_dhToLR_link_rand_swap (F := F) gen hg A).symm]
    exact QueryImpl.Stateful.advantage_self _ _ _
  -- Hop #5: G₄.advantage elgamalLR_right A = 0
  have h5 : G₄.advantage (PUnit.unit, none) (elgamalLR_right (F := F) gen) none A = 0 := by
    rw [hG₄, QueryImpl.Stateful.advantage_eq_of_evalDist_runProb_eq
      (evalDist_runProb_dhToLR_right_link_real_eq_elgamalLR_right (F := F) gen A)]
    exact QueryImpl.Stateful.advantage_self _ _ _
  -- Hop #2: G₁.advantage G₂ A = (dhTripleReal).advantage (dhTripleRand) (shiftLeft dhToLR_left A)
  have h2 : G₁.advantage (PUnit.unit, none) G₂ (PUnit.unit, none) A =
      (dhTripleReal (F := F) gen).advantage none (dhTripleRand (F := F) gen) none
        (dhToLR_left.shiftLeft PUnit.unit A) := by
    rw [hG₁, hG₂, QueryImpl.Stateful.advantage_link_left_eq_advantage_shiftLeft]
  -- Hop #4: G₃.advantage G₄ A = (dhTripleReal).advantage (dhTripleRand) (shiftLeft dhToLR_right A)
  have h4 : G₃.advantage (PUnit.unit, none) G₄ (PUnit.unit, none) A =
      (dhTripleReal (F := F) gen).advantage none (dhTripleRand (F := F) gen) none
        (dhToLR_right.shiftLeft PUnit.unit A) := by
    rw [hG₃, hG₄, QueryImpl.Stateful.advantage_link_left_eq_advantage_shiftLeft,
      QueryImpl.Stateful.advantage_symm]
  -- Four applications of the triangle inequality collapse the chain.
  calc (elgamalLR_left (F := F) gen).advantage none (elgamalLR_right (F := F) gen) none A
      ≤ (elgamalLR_left (F := F) gen).advantage none G₁ (PUnit.unit, none) A
          + G₁.advantage (PUnit.unit, none) (elgamalLR_right (F := F) gen) none A :=
            QueryImpl.Stateful.advantage_triangle _ _ _ _ _ _ _
    _ ≤ (elgamalLR_left (F := F) gen).advantage none G₁ (PUnit.unit, none) A
          + (G₁.advantage (PUnit.unit, none) G₂ (PUnit.unit, none) A
            + G₂.advantage (PUnit.unit, none) (elgamalLR_right (F := F) gen) none A) := by
        gcongr
        exact QueryImpl.Stateful.advantage_triangle _ _ _ _ _ _ _
    _ ≤ (elgamalLR_left (F := F) gen).advantage none G₁ (PUnit.unit, none) A
          + (G₁.advantage (PUnit.unit, none) G₂ (PUnit.unit, none) A
            + (G₂.advantage (PUnit.unit, none) G₃ (PUnit.unit, none) A
              + G₃.advantage (PUnit.unit, none) (elgamalLR_right (F := F) gen) none A)) := by
        gcongr
        exact QueryImpl.Stateful.advantage_triangle _ _ _ _ _ _ _
    _ ≤ (elgamalLR_left (F := F) gen).advantage none G₁ (PUnit.unit, none) A
          + (G₁.advantage (PUnit.unit, none) G₂ (PUnit.unit, none) A
            + (G₂.advantage (PUnit.unit, none) G₃ (PUnit.unit, none) A
              + (G₃.advantage (PUnit.unit, none) G₄ (PUnit.unit, none) A
                + G₄.advantage (PUnit.unit, none) (elgamalLR_right (F := F) gen) none A))) := by
        gcongr
        exact QueryImpl.Stateful.advantage_triangle _ _ _ _ _ _ _
    _ = G₁.advantage (PUnit.unit, none) G₂ (PUnit.unit, none) A
        + G₃.advantage (PUnit.unit, none) G₄ (PUnit.unit, none) A := by
        rw [h1, h3, h5]
        ring
    _ = (dhTripleReal (F := F) gen).advantage none (dhTripleRand (F := F) gen)
          none (dhToLR_left.shiftLeft PUnit.unit A)
        + (dhTripleReal (F := F) gen).advantage none (dhTripleRand (F := F) gen)
          none (dhToLR_right.shiftLeft PUnit.unit A) := by rw [h2, h4]

end VCVio.StateSeparating.Examples.ElGamal
