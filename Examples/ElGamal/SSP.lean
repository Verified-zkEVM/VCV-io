/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.SSP.Hybrid

/-!
# State-Separating Proofs: ElGamal IND-CPA via DDH

A package-level formulation of the many-query *left-or-right* IND-CPA game for ElGamal in the
SSProve style. The example wraps the ElGamal / DDH machinery from `Examples.ElGamal.Basic` and
`VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman` into the `Package` API of
`VCVio.SSP`, illustrating how the SSP combinators (`link`, `advantage`, `shiftLeft`,
`advantage_hybrid`) organize a security proof.

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
distribution. It is implementation-equivalent to standard DDH up to a hybrid argument over
the queries; the reduction to the single-query `DDHAdversary` is stated below as a placeholder
lemma (`dhTriple_advantage_le_single_query_ddh`) and left to future work.

## Game packages

* `elgamalLR_left F gen` and `elgamalLR_right F gen` are the two LR-style games. The secret
  key `sk` is *lazily sampled* on the first `GETPK` or `LR` query and cached in the package
  state `Option F` so that all subsequent queries share the same `sk`. Each `LR` query samples
  fresh randomness `r`, producing independent encryptions under the shared key.
* `dhTripleReal F gen` and `dhTripleRand F gen` are the corresponding "real" and "random" DDH
  packages. They cache the secret exponent `a` lazily (state `Option F`) and sample fresh
  per-query exponents `b` (and `c` in the random case). Each `GETPK` answer thus uses a
  consistent `pk = a • gen` across queries, while each `DHCHALLENGE` uses fresh `b`.

## Reduction packages

* `dhToLR_leftHandler` and `dhToLR_rightHandler` are stateless reduction handlers. Each LR
  query is forwarded to the corresponding DDH oracle, then projected: `GETPK` is forwarded
  unchanged, while `LR (m₀, m₁)` maps `DHCHALLENGE`'s `(B, T)` to the ciphertext `(B, T + m_b)`
  for `m_b ∈ {m₀, m₁}`.
* `dhToLR_left` and `dhToLR_right` are the corresponding `Package`s built via
  `Package.ofStateless`.

## SSP-style hybrid bound

The classical 5-game / 4-hop hybrid

```
elgamalLR_left  ↔  dhToLR_left.link dhTripleReal
                ≈  dhToLR_left.link dhTripleRand   -- multi-query DDH gap
                ↔  dhToLR_right.link dhTripleRand  -- rand-swap symmetry
                ≈  dhToLR_right.link dhTripleReal  -- multi-query DDH gap
                ↔  elgamalLR_right
```

collapses through `Package.advantage_triangle` and
`Package.advantage_link_left_eq_advantage_shiftLeft` into the bound on `elgamalLR_left`
versus `elgamalLR_right`. The boundary program-equivalence steps (1, 5) are discharged below
as the named `evalDist_runProb_*` lemmas; the rand-swap step (3) is stated as
`evalDist_runProb_dhToLR_left_link_rand_eq_dhToLR_right_link_rand` with a `sorry` pending the
uniform-masking reduction (analogous to `IND_CPA_OneTime_DDHReduction_rand_half` in
`Examples.ElGamal.Basic`).
The multi-query-to-single-query DDH reduction (steps 2, 4) is stated as
`dhTriple_advantage_le_single_query_ddh` with a `sorry` pending the hybrid argument over
queries. The final bound `elgamalLR_left_advantage_le` combines the four hops into an
end-to-end advantage bound.
-/

open OracleSpec OracleComp ProbComp VCVio.SSP

namespace VCVio.SSP.Examples.ElGamal

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

variable {F : Type} [Field F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-! ### DDH triple packages -/

/-- The "real" DDH package (multi-query, shared-`a`).

The first exponent `a` is lazily sampled on first access and cached in the state. `GETPK`
returns `a • gen` and `DHCHALLENGE` returns `(b • gen, (a * b) • gen)` for fresh `b`. -/
noncomputable def dhTripleReal (gen : G) :
    Package unifSpec (dhSpec G) (Option F) where
  init := none
  impl
    | Sum.inl _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F : ProbComp F)
            pure (a • gen, some a)
        | some a => pure (a • gen, some a)
    | Sum.inr _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F : ProbComp F)
            let b ← ($ᵗ F : ProbComp F)
            pure ((b • gen, (a * b) • gen), some a)
        | some a => do
            let b ← ($ᵗ F : ProbComp F)
            pure ((b • gen, (a * b) • gen), some a)

/-- The "random" DDH package (multi-query, shared-`a`). Identical to `dhTripleReal` except
`DHCHALLENGE` returns `(b • gen, c • gen)` for fresh `b, c`. -/
noncomputable def dhTripleRand (gen : G) :
    Package unifSpec (dhSpec G) (Option F) where
  init := none
  impl
    | Sum.inl _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F : ProbComp F)
            pure (a • gen, some a)
        | some a => pure (a • gen, some a)
    | Sum.inr _ => fun st => match st with
        | none => do
            let a ← ($ᵗ F : ProbComp F)
            let b ← ($ᵗ F : ProbComp F)
            let c ← ($ᵗ F : ProbComp F)
            pure ((b • gen, c • gen), some a)
        | some a => do
            let b ← ($ᵗ F : ProbComp F)
            let c ← ($ᵗ F : ProbComp F)
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
    Package unifSpec (lrSpec G) (Option F) where
  init := none
  impl
    | Sum.inl _ => fun st => match st with
        | none => do
            let sk ← ($ᵗ F : ProbComp F)
            pure (sk • gen, some sk)
        | some sk => pure (sk • gen, some sk)
    | Sum.inr (m₀, _) => fun st => match st with
        | none => do
            let sk ← ($ᵗ F : ProbComp F)
            let r ← ($ᵗ F : ProbComp F)
            pure ((r • gen, (sk * r) • gen + m₀), some sk)
        | some sk => do
            let r ← ($ᵗ F : ProbComp F)
            pure ((r • gen, (sk * r) • gen + m₀), some sk)

/-- The "right-message" ElGamal LR game. Same as `elgamalLR_left` except `LR (_, m₁)` returns
`(r • gen, (sk * r) • gen + m₁)`. -/
noncomputable def elgamalLR_right (gen : G) :
    Package unifSpec (lrSpec G) (Option F) where
  init := none
  impl
    | Sum.inl _ => fun st => match st with
        | none => do
            let sk ← ($ᵗ F : ProbComp F)
            pure (sk • gen, some sk)
        | some sk => pure (sk • gen, some sk)
    | Sum.inr (_, m₁) => fun st => match st with
        | none => do
            let sk ← ($ᵗ F : ProbComp F)
            let r ← ($ᵗ F : ProbComp F)
            pure ((r • gen, (sk * r) • gen + m₁), some sk)
        | some sk => do
            let r ← ($ᵗ F : ProbComp F)
            pure ((r • gen, (sk * r) • gen + m₁), some sk)

/-! ### DDH-to-LR reductions -/

/-- Stateless reduction handler encrypting the *left* message. Forwards `GETPK` on `lr`
to `GETPK` on `dh`, and forwards `LR (m₀, _)` to `DHCHALLENGE` on `dh`, returning the pair
`(B, T + m₀)` from the DDH challenge `(B, T)`. -/
def dhToLR_leftHandler {G : Type} [Add G] :
    QueryImpl (lrSpec G) (OracleComp (dhSpec G))
  | Sum.inl _ => (query (spec := dhSpec G) (Sum.inl ()) : OracleComp (dhSpec G) G)
  | Sum.inr (m₀, _) => do
      let bt ← (query (spec := dhSpec G) (Sum.inr ()) : OracleComp (dhSpec G) (G × G))
      pure (bt.1, bt.2 + m₀)

/-- Stateless reduction handler encrypting the *right* message. -/
def dhToLR_rightHandler {G : Type} [Add G] :
    QueryImpl (lrSpec G) (OracleComp (dhSpec G))
  | Sum.inl _ => (query (spec := dhSpec G) (Sum.inl ()) : OracleComp (dhSpec G) G)
  | Sum.inr (_, m₁) => do
      let bt ← (query (spec := dhSpec G) (Sum.inr ()) : OracleComp (dhSpec G) (G × G))
      pure (bt.1, bt.2 + m₁)

/-- DDH-to-LR reduction encrypting the left message, packaged as a stateless `Package`. -/
def dhToLR_left {G : Type} [Add G] : Package (dhSpec G) (lrSpec G) PUnit.{1} :=
  Package.ofStateless dhToLR_leftHandler

/-- DDH-to-LR reduction encrypting the right message, packaged as a stateless `Package`. -/
def dhToLR_right {G : Type} [Add G] : Package (dhSpec G) (lrSpec G) PUnit.{1} :=
  Package.ofStateless dhToLR_rightHandler

/-! ### Reduction equivalences (Hops #1 and #5)

Each of the two named lemmas below shows that two SSP packages produce the same
distribution against any adversary `A`. They are the SSP-level analogues of the rewrites in
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
    evalDist
        ((simulateQ (dhTripleReal (F := F) gen).impl
          ((dhToLR_leftHandler (G := G)) q)).run s) =
      evalDist (((elgamalLR_left (F := F) gen).impl q).run s) := by
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
    evalDist
        ((simulateQ (dhTripleReal (F := F) gen).impl
          ((dhToLR_rightHandler (G := G)) q)).run s) =
      evalDist (((elgamalLR_right (F := F) gen).impl q).run s) := by
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

/-- Hop #1: the SSP-level analogue of `IND_CPA_OneTime_game_evalDist_eq_ddhExpReal`: linking
the DDH-real package under the *left*-message reduction produces the same output distribution
as the LR-left game itself. -/
theorem evalDist_runProb_dhToLR_left_link_real_eq_elgamalLR_left
    (gen : G) {α : Type} (A : OracleComp (lrSpec G) α) :
    evalDist ((dhToLR_left.link (dhTripleReal (F := F) gen)).runProb A) =
      evalDist ((elgamalLR_left (F := F) gen).runProb A) := by
  unfold Package.runProb
  rw [show dhToLR_left = Package.ofStateless (dhToLR_leftHandler (G := G)) from rfl,
    Package.run_link_left_ofStateless]
  unfold Package.run
  rw [StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  exact Package.simulateQ_StateT_evalDist_congr
    (composed_real_left_handler_evalDist (F := F) gen) A none

/-- Hop #5: the right-message analogue of
`evalDist_runProb_dhToLR_left_link_real_eq_elgamalLR_left`. -/
theorem evalDist_runProb_dhToLR_right_link_real_eq_elgamalLR_right
    (gen : G) {α : Type} (A : OracleComp (lrSpec G) α) :
    evalDist ((dhToLR_right.link (dhTripleReal (F := F) gen)).runProb A) =
      evalDist ((elgamalLR_right (F := F) gen).runProb A) := by
  unfold Package.runProb
  rw [show dhToLR_right = Package.ofStateless (dhToLR_rightHandler (G := G)) from rfl,
    Package.run_link_left_ofStateless]
  unfold Package.run
  rw [StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  exact Package.simulateQ_StateT_evalDist_congr
    (composed_real_right_handler_evalDist (F := F) gen) A none

end ReductionEquivalences

/-! ### Rand-swap symmetry (Hop #3, placeholder)

The middle hop of the hybrid equates `dhToLR_left.link dhTripleRand` and
`dhToLR_right.link dhTripleRand` as distributions. Under `dhTripleRand`, the DDH-challenge
oracle returns a fresh, uniform third component `c • gen`; assuming `(· • gen) : F → G` is
bijective, this third component is a uniform element of `G` and acts as a one-time pad
additively masking `m₀` or `m₁`. Pointwise, `(b • gen, c • gen + m₀)` and
`(b • gen, c • gen + m₁)` therefore have the same distribution; the argument is the SSP
analogue of `Examples.ElGamal.Basic.IND_CPA_OneTime_DDHReduction_rand_half` and uses
`ElGamalExamples.uniformMaskedCipher_bind_dist_indep`. The actual proof is left as future
work. -/

/-- Hop #3 placeholder: under the DDH-random package, the left- and right-message reductions
produce the same output distribution against any adversary. Requires bijectivity of
`(· • gen)`; the proof is an SSP lift of the uniform-masking argument and is left as `sorry`. -/
theorem evalDist_runProb_dhToLR_left_link_rand_eq_dhToLR_right_link_rand
    (gen : G) (_hg : Function.Bijective (fun x : F => x • gen))
    {α : Type} (A : OracleComp (lrSpec G) α) :
    evalDist ((dhToLR_left.link (dhTripleRand (F := F) gen)).runProb A) =
      evalDist ((dhToLR_right.link (dhTripleRand (F := F) gen)).runProb A) := by
  sorry

/-! ### Multi-query to single-query DDH reduction (Hops #2 and #4, placeholder)

The SSP package `dhTripleReal` versus `dhTripleRand` encodes the *multi-query, shared-`a`*
DDH distribution. Bounding its distinguishing advantage by the standard single-query DDH
advantage requires a hybrid argument over the queries issued by the shifted adversary. Only
the statement is provided below. -/

/-- Hop #2/#4 placeholder: the multi-query, shared-`a` DDH distinguishing advantage is bounded
by the single-query DDH guess advantage of some extracted `DDHAdversary`. The extraction goes
via a standard hybrid over the `DHCHALLENGE` queries issued by `A`; the proof is left as
`sorry` pending the hybrid formalization. -/
theorem dhTriple_advantage_le_single_query_ddh (gen : G) (A : OracleComp (dhSpec G) Bool) :
    ∃ (adv : DiffieHellman.DDHAdversary F G),
      (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen) A ≤
        DiffieHellman.ddhGuessAdvantage gen adv := by
  sorry

/-! ### End-to-end advantage bound

The headline security statement: the many-query LR-IND-CPA advantage of ElGamal is bounded by
twice the multi-query DDH advantage (one term per message slot). Combined with
`dhTriple_advantage_le_single_query_ddh` (once filled in), this yields the full SSP-style
reduction to standard DDH. -/

/-- The advantage of distinguishing `elgamalLR_left gen` from `elgamalLR_right gen` is bounded
by the sum of two multi-query DDH advantages, one against the shifted left-message reduction
adversary and one against the shifted right-message reduction adversary. -/
theorem elgamalLR_left_advantage_right_le
    (gen : G) (hg : Function.Bijective (fun x : F => x • gen))
    (A : OracleComp (lrSpec G) Bool) :
    (elgamalLR_left (F := F) gen).advantage (elgamalLR_right (F := F) gen) A ≤
      (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen)
          (dhToLR_left.shiftLeft A)
      + (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen)
          (dhToLR_right.shiftLeft A) := by
  set G₁ := dhToLR_left.link (dhTripleReal (F := F) gen) with hG₁
  set G₂ := dhToLR_left.link (dhTripleRand (F := F) gen) with hG₂
  set G₃ := dhToLR_right.link (dhTripleRand (F := F) gen) with hG₃
  set G₄ := dhToLR_right.link (dhTripleReal (F := F) gen) with hG₄
  -- Hop #1: (elgamalLR_left).advantage G₁ A = 0
  have h1 : (elgamalLR_left (F := F) gen).advantage G₁ A = 0 := by
    rw [hG₁, Package.advantage_eq_of_evalDist_runProb_eq_right
      (evalDist_runProb_dhToLR_left_link_real_eq_elgamalLR_left (F := F) gen A)]
    exact Package.advantage_self _ _
  -- Hop #3: G₂.advantage G₃ A = 0
  have h3 : G₂.advantage G₃ A = 0 := by
    rw [hG₂, hG₃, Package.advantage_eq_of_evalDist_runProb_eq_right
      (evalDist_runProb_dhToLR_left_link_rand_eq_dhToLR_right_link_rand (F := F) gen hg A).symm]
    exact Package.advantage_self _ _
  -- Hop #5: G₄.advantage elgamalLR_right A = 0
  have h5 : G₄.advantage (elgamalLR_right (F := F) gen) A = 0 := by
    rw [hG₄, Package.advantage_eq_of_evalDist_runProb_eq
      (evalDist_runProb_dhToLR_right_link_real_eq_elgamalLR_right (F := F) gen A)]
    exact Package.advantage_self _ _
  -- Hop #2: G₁.advantage G₂ A = (dhTripleReal).advantage (dhTripleRand) (shiftLeft dhToLR_left A)
  have h2 : G₁.advantage G₂ A =
      (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen)
        (dhToLR_left.shiftLeft A) := by
    rw [hG₁, hG₂, Package.advantage_link_left_eq_advantage_shiftLeft]
  -- Hop #4: G₃.advantage G₄ A = (dhTripleReal).advantage (dhTripleRand) (shiftLeft dhToLR_right A)
  have h4 : G₃.advantage G₄ A =
      (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen)
        (dhToLR_right.shiftLeft A) := by
    rw [hG₃, hG₄, Package.advantage_link_left_eq_advantage_shiftLeft,
      Package.advantage_symm]
  -- Four applications of the triangle inequality collapse the chain.
  calc (elgamalLR_left (F := F) gen).advantage (elgamalLR_right (F := F) gen) A
      ≤ (elgamalLR_left (F := F) gen).advantage G₁ A
          + G₁.advantage (elgamalLR_right (F := F) gen) A := Package.advantage_triangle _ _ _ _
    _ ≤ (elgamalLR_left (F := F) gen).advantage G₁ A
          + (G₁.advantage G₂ A + G₂.advantage (elgamalLR_right (F := F) gen) A) := by
        gcongr
        exact Package.advantage_triangle _ _ _ _
    _ ≤ (elgamalLR_left (F := F) gen).advantage G₁ A
          + (G₁.advantage G₂ A
            + (G₂.advantage G₃ A + G₃.advantage (elgamalLR_right (F := F) gen) A)) := by
        gcongr
        exact Package.advantage_triangle _ _ _ _
    _ ≤ (elgamalLR_left (F := F) gen).advantage G₁ A
          + (G₁.advantage G₂ A
            + (G₂.advantage G₃ A
              + (G₃.advantage G₄ A + G₄.advantage (elgamalLR_right (F := F) gen) A))) := by
        gcongr
        exact Package.advantage_triangle _ _ _ _
    _ = G₁.advantage G₂ A + G₃.advantage G₄ A := by rw [h1, h3, h5]; ring
    _ = (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen)
          (dhToLR_left.shiftLeft A)
        + (dhTripleReal (F := F) gen).advantage (dhTripleRand (F := F) gen)
          (dhToLR_right.shiftLeft A) := by rw [h2, h4]

end VCVio.SSP.Examples.ElGamal
