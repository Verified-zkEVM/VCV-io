/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ElGamal.Common
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.SSP.Hybrid

/-!
# State-Separating Proofs: ElGamal IND-CPA via DDH

A package-level reformulation of one-time IND-CPA security for ElGamal. The example wraps the
existing ElGamal / DDH machinery in `Examples.ElGamal.Basic` and
`VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman` into the `Package` API of
`VCVio.SSP`, illustrating how the SSP combinators (`link`, `advantage`, `shiftLeft`,
`advantage_hybrid`) can be used to organize a security proof in the SSProve style.

## Oracle interfaces

* `lrSpec G` is the export interface of the IND-CPA challenger: a single oracle taking a pair
  of messages `(m₀, m₁) : G × G` and returning an ElGamal-shaped ciphertext `(c₁, c₂) : G × G`.
* `dhSpec G` is the import interface of the DDH game: a single oracle returning a triple
  `(A, B, T) : G × G × G`.

## Game packages

For a fixed generator `gen : G`:

* `elgamalLR_left F gen` and `elgamalLR_right F gen` are the two LR-style games. Each query
  samples a fresh secret key and randomness and returns the ElGamal encryption of the
  designated message under that fresh key.
* `dhTripleReal F gen` and `dhTripleRand F gen` are the standard "real" and "random" DDH
  triple packages.

## Reduction packages

* `dhToLR_left` and `dhToLR_right` reduce the LR challenge to a DDH triple query: the
  reduction interprets the DDH triple `(A, B, T)` by treating `A` as the public key, `B` as
  the encryption randomness's group element, and `T` as the DH shared mask, returning the
  ciphertext `(B, T + m)` for `m ∈ {m₀, m₁}`.

## SSP-style hybrid bound

The classical 4-game hybrid

```
elgamalLR_left  ↔  dhToLR_left.link dhTripleReal
                ↔  dhToLR_left.link dhTripleRand   -- DDH gap
                ↔  dhToLR_right.link dhTripleRand  -- 0 (uniform mask)
                ↔  dhToLR_right.link dhTripleReal
                ↔  elgamalLR_right
```

collapses through `Package.advantage_triangle`,
`Package.advantage_link_left_eq_advantage_shiftLeft`, and `Package.advantage_symm` into the
bound `advantage_elgamalLR_le_advantage_dh_real_rand`. The intermediate program-equivalence
steps (1, 3, 5) are discharged as the named `runProb_dhToLR_*` /
`evalDist_runProb_dhToLR_*` lemmas below, using the same kind of `evalDist` rewrites that
`Examples.ElGamal.Basic.IND_CPA_OneTime_game_evalDist_eq_ddhExpReal` performs for the
bit-mixed reduction.
-/

universe u

open OracleSpec OracleComp ProbComp VCVio.SSP

namespace VCVio.SSP.Examples.ElGamal

/-! ### Oracle interfaces -/

/-- The LR oracle interface: input a pair of messages, output an ElGamal-shaped ciphertext. -/
@[reducible] def lrSpec (G : Type) : OracleSpec (G × G) := (G × G) →ₒ (G × G)

/-- The DDH triple interface: a single oracle returning a triple `(A, B, T) : G × G × G`. -/
@[reducible] def dhSpec (G : Type) : OracleSpec Unit := Unit →ₒ (G × G × G)

/-! ### DDH triple packages -/

/-- The "real" DDH triple package: each query returns `(a • gen, b • gen, (a * b) • gen)` for
fresh `a, b ← F`. This is the package-level form of `DiffieHellman.ddhExpReal` with the
adversary stripped out. -/
noncomputable def dhTripleReal (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {G : Type} [AddCommGroup G] [Module F G] (gen : G) :
    Package unifSpec (dhSpec G) PUnit.{1} :=
  Package.ofStateless fun _ => do
    let a ← ($ᵗ F : ProbComp F)
    let b ← ($ᵗ F : ProbComp F)
    pure (a • gen, b • gen, (a * b) • gen)

/-- The "random" DDH triple package: each query returns `(a • gen, b • gen, c • gen)` for
fresh `a, b, c ← F`. This is the package-level form of `DiffieHellman.ddhExpRand`. -/
noncomputable def dhTripleRand (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {G : Type} [AddCommGroup G] [Module F G] (gen : G) :
    Package unifSpec (dhSpec G) PUnit.{1} :=
  Package.ofStateless fun _ => do
    let a ← ($ᵗ F : ProbComp F)
    let b ← ($ᵗ F : ProbComp F)
    let c ← ($ᵗ F : ProbComp F)
    pure (a • gen, b • gen, c • gen)

/-! ### ElGamal LR-style games

Each LR query samples a *fresh* secret key on the spot. This matches the one-time IND-CPA
framing used in `Examples.ElGamal.Basic`: the key never has to be reused across queries
because the SSP analysis collapses to a single LR call via the standard reduction. -/

/-- The "left-message" ElGamal LR game: each query encrypts the *first* message of the pair
under a fresh key, returning the resulting ElGamal ciphertext. -/
noncomputable def elgamalLR_left (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {G : Type} [AddCommGroup G] [Module F G] (gen : G) :
    Package unifSpec (lrSpec G) PUnit.{1} :=
  Package.ofStateless fun (m₀, _) => do
    let sk ← ($ᵗ F : ProbComp F)
    let r ← ($ᵗ F : ProbComp F)
    pure (r • gen, m₀ + r • (sk • gen))

/-- The "right-message" ElGamal LR game: each query encrypts the *second* message of the pair
under a fresh key. -/
noncomputable def elgamalLR_right (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {G : Type} [AddCommGroup G] [Module F G] (gen : G) :
    Package unifSpec (lrSpec G) PUnit.{1} :=
  Package.ofStateless fun (_, m₁) => do
    let sk ← ($ᵗ F : ProbComp F)
    let r ← ($ᵗ F : ProbComp F)
    pure (r • gen, m₁ + r • (sk • gen))

/-! ### DDH-to-LR reductions

These two packages reduce the LR challenge to a single DDH triple query. They differ only in
which of the two adversary-supplied messages they encrypt; the symmetry between them is what
lets a uniform DH mask hide the choice. -/

/-- DDH-to-LR reduction encrypting the *left* message: query the DDH triple oracle for
`(A, B, T)` and return the ciphertext `(B, T + m₀)`. -/
def dhToLR_left {G : Type} [Add G] : Package (dhSpec G) (lrSpec G) PUnit.{1} :=
  Package.ofStateless fun (m₀, _) => do
    let triple ← (query (spec := dhSpec G) () : OracleComp (dhSpec G) (G × G × G))
    let (_, B, T) := triple
    pure (B, T + m₀)

/-- DDH-to-LR reduction encrypting the *right* message: query the DDH triple oracle for
`(A, B, T)` and return the ciphertext `(B, T + m₁)`. -/
def dhToLR_right {G : Type} [Add G] : Package (dhSpec G) (lrSpec G) PUnit.{1} :=
  Package.ofStateless fun (_, m₁) => do
    let triple ← (query (spec := dhSpec G) () : OracleComp (dhSpec G) (G × G × G))
    let (_, B, T) := triple
    pure (B, T + m₁)

section ReductionEquivalences

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-! ### Reduction equivalences

The three program equivalences below justify the structural steps of the IND-CPA-via-DDH
reduction:

* `runProb_dhToLR_left_link_real_eq_elgamalLR_left` and the analogous `_right` lemma identify
  the DDH-real branch of the reduction with the corresponding ElGamal LR game.
* `runProb_dhToLR_link_rand_swap` is the message-swap symmetry: the DDH-random branch is
  independent of which message was selected, so the two reductions agree as `ProbComp`s.

These are stated as `runProb` equalities because that is the form `Package.advantage`
operates on; once they are available, the final advantage bound is purely algebraic. -/

omit [SampleableType G] in
/-- Linking `dhToLR_left` with the *real* DDH triple package recovers the ElGamal LR-left
game. Substituting `pk = a • gen` and `r = b` aligns the freshly sampled DDH exponents with
ElGamal's key and randomness. -/
theorem runProb_dhToLR_left_link_real_eq_elgamalLR_left (gen : G)
    (A : OracleComp (lrSpec G) Bool) :
    (dhToLR_left.link (dhTripleReal F gen)).runProb A =
      (elgamalLR_left F gen).runProb A := by
  -- Unfold both sides to `simulateQ <handler> A` and reduce to handler equality.
  change ((dhToLR_left (G := G)).link (dhTripleReal F gen)).run A = (elgamalLR_left F gen).run A
  unfold dhToLR_left dhTripleReal elgamalLR_left
  rw [Package.run_link_ofStateless, ← QueryImpl.simulateQ_compose, Package.run_ofStateless]
  congr 1
  ext ⟨m₀, m₁⟩
  -- Composed handler on (m₀, m₁) ≡ ElGamal LR-left handler on (m₀, m₁).
  -- Unfold the composition and the inner DDH-triple sample.
  simp only [QueryImpl.apply_compose, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun b => ?_
  -- Now both sides are `pure (b • gen, _)`; reduce to scalar/group equality.
  refine congrArg pure ?_
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  -- Goal: m₀ + a • b • gen = m₀ + b • a • gen, i.e. m₀ + (a*b) • gen = m₀ + (b*a) • gen.
  rw [add_comm m₀, ← mul_smul, mul_comm a b, mul_smul]

omit [SampleableType G] in
/-- Linking `dhToLR_right` with the real DDH triple package recovers the ElGamal LR-right
game. -/
theorem runProb_dhToLR_right_link_real_eq_elgamalLR_right (gen : G)
    (A : OracleComp (lrSpec G) Bool) :
    (dhToLR_right.link (dhTripleReal F gen)).runProb A =
      (elgamalLR_right F gen).runProb A := by
  -- Same proof as `_left`: the only difference is which message is added to the mask.
  change ((dhToLR_right (G := G)).link (dhTripleReal F gen)).run A = (elgamalLR_right F gen).run A
  unfold dhToLR_right dhTripleReal elgamalLR_right
  rw [Package.run_link_ofStateless, ← QueryImpl.simulateQ_compose, Package.run_ofStateless]
  congr 1
  ext ⟨m₀, m₁⟩
  simp only [QueryImpl.apply_compose, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun b => ?_
  refine congrArg pure ?_
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
  rw [add_comm m₁, ← mul_smul, mul_comm a b, mul_smul]

/-- Swap symmetry for the random-DDH branch: when the DH triple's third component is uniform
and independent of the messages, the choice between encrypting `m₀` and `m₁` is statistically
invisible. The two linked games agree under `evalDist`. The proof is the SSP-flavoured
analogue of `Examples.ElGamal.Basic.IND_CPA_OneTime_DDHReduction_rand_half`. -/
theorem evalDist_runProb_dhToLR_link_rand_swap (gen : G)
    (hg : Function.Bijective (· • gen : F → G))
    (A : OracleComp (lrSpec G) Bool) :
    evalDist ((dhToLR_left.link (dhTripleRand F gen)).runProb A) =
      evalDist ((dhToLR_right.link (dhTripleRand F gen)).runProb A) := by
  -- Reduce both sides to a `simulateQ`, then to handler-equality (under `evalDist`).
  change evalDist (((dhToLR_left (G := G)).link (dhTripleRand F gen)).run A) =
    evalDist (((dhToLR_right (G := G)).link (dhTripleRand F gen)).run A)
  unfold dhToLR_left dhToLR_right dhTripleRand
  rw [Package.run_link_ofStateless, Package.run_link_ofStateless,
    ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  refine Package.simulateQ_evalDist_congr ?_ A
  rintro ⟨m₀, m₁⟩
  -- After unfolding the composition, both sides are
  -- `do let a; let b; let c; pure (b • gen, c • gen + m_b)`.
  simp only [QueryImpl.apply_compose, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.cont_query, OracleQuery.input_query, id_map, bind_assoc, pure_bind]
  -- Reduce both sides via a key lemma: under uniform sampling, `c • gen + m` is uniform on `G`.
  -- Both sides become `($ᵗ F) >>= fun _ => ($ᵗ F) >>= fun b => ($ᵗ G) >>= fun p => pure (b•gen,p)`.
  have key : ∀ m : G,
      evalDist (($ᵗ F : ProbComp F) >>= fun _ => ($ᵗ F : ProbComp F) >>= fun b =>
          ($ᵗ F : ProbComp F) >>= fun c => pure ((b • gen, c • gen + m) : G × G))
      = evalDist (($ᵗ F : ProbComp F) >>= fun _ => ($ᵗ F : ProbComp F) >>= fun b =>
          ($ᵗ G : ProbComp G) >>= fun p => pure ((b • gen, p) : G × G)) := by
    intro m
    -- The key step: `(c ↦ c • gen + m)` is a bijection F → G.
    have hbij : Function.Bijective (fun c : F => c • gen + m) := by
      change Function.Bijective ((· + m) ∘ (· • gen : F → G))
      refine Function.Bijective.comp ?_ hg
      exact ⟨fun a b h => add_right_cancel h, fun y => ⟨y - m, sub_add_cancel y m⟩⟩
    -- Show pointwise equality of probabilities.
    refine evalDist_ext fun y => ?_
    refine probOutput_bind_congr' _ y fun _ => ?_
    refine probOutput_bind_congr' _ y fun b => ?_
    -- Goal: Pr[= y | $ᵗ F >>= fun c => pure (b•gen, c•gen + m)]
    --     = Pr[= y | $ᵗ G >>= fun p => pure (b•gen, p)]
    have h₁ : (($ᵗ F : ProbComp F) >>= fun c => pure ((b • gen, c • gen + m) : G × G))
        = ((fun p : G => ((b • gen, p) : G × G)) ∘ (fun c : F => c • gen + m)) <$>
          ($ᵗ F : ProbComp F) := by
      rw [map_eq_bind_pure_comp]; rfl
    have h₂ : (($ᵗ G : ProbComp G) >>= fun p => pure ((b • gen, p) : G × G))
        = (fun p : G => ((b • gen, p) : G × G)) <$> ($ᵗ G : ProbComp G) := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [h₁, h₂]
    -- Rewrite LHS as `g <$> (f <$> $ᵗ F)` and use bijectivity of `f`.
    have hcomp : ((fun p : G => ((b • gen, p) : G × G)) ∘ (fun c : F => c • gen + m)) <$>
        ($ᵗ F : ProbComp F)
        = (fun p : G => ((b • gen, p) : G × G)) <$>
          ((fun c : F => c • gen + m) <$> ($ᵗ F : ProbComp F)) := by
      rw [Function.comp_def]; exact (Functor.map_map _ _ _).symm
    rw [hcomp]
    exact probOutput_map_eq_of_evalDist_eq
      (evalDist_map_bijective_uniform_cross (α := F) (β := G) _ hbij) _ _
  -- Combine the two instances at `m₀` and `m₁` via the common right-hand side.
  exact (key m₀).trans (key m₁).symm

/-! ### Final SSP advantage bound -/

/-- **One-time SSP IND-CPA bound for ElGamal.** The distinguishing advantage between the
left- and right-message ElGamal LR games is bounded by the sum of two DDH advantages, one for
each of the two reduction packages.

This is the SSP-style restatement of the bound in `Examples.ElGamal.Basic`: instead of
factoring the advantage through a single bit-mixed reduction, we hop through the four-game
chain spelled out in the module docstring and sum the consecutive advantages with
`Package.advantage_triangle`, applying the SSP reduction lemma
`Package.advantage_link_left_eq_advantage_shiftLeft` to absorb the reduction packages into
shifted adversaries. The intermediate program-equivalence steps (1, 3, 5) are discharged by
the three `runProb_*` lemmas above. -/
theorem advantage_elgamalLR_le_advantage_dh_real_rand (gen : G)
    (hg : Function.Bijective (· • gen : F → G))
    (A : OracleComp (lrSpec G) Bool) :
    (elgamalLR_left F gen).advantage (elgamalLR_right F gen) A ≤
      (dhTripleReal F gen).advantage (dhTripleRand F gen)
        ((dhToLR_left (G := G)).shiftLeft A) +
      (dhTripleReal F gen).advantage (dhTripleRand F gen)
        ((dhToLR_right (G := G)).shiftLeft A) := by
  -- Hybrid chain in `runProb` form:
  --   G₀ = elgamalLR_left
  --   G₁ = dhToLR_left.link dhTripleReal   (= G₀ by step 1)
  --   G₂ = dhToLR_left.link dhTripleRand   (Adv with G₁ = DDH advantage of left shift)
  --   G₃ = dhToLR_right.link dhTripleRand  (= G₂ by step 3, swap symmetry)
  --   G₄ = dhToLR_right.link dhTripleReal  (Adv with G₃ = DDH advantage of right shift)
  --   G₅ = elgamalLR_right                  (= G₄ by step 5)
  -- Step 1 + 5: identify endpoints with the linked-game forms.
  have hL : (elgamalLR_left F gen).advantage (elgamalLR_right F gen) A =
      (dhToLR_left.link (dhTripleReal F gen)).advantage
        (dhToLR_right.link (dhTripleReal F gen)) A := by
    refine (Package.advantage_eq_of_evalDist_runProb_eq ?_).trans
      (Package.advantage_eq_of_evalDist_runProb_eq_right ?_)
    · exact congrArg _ (runProb_dhToLR_left_link_real_eq_elgamalLR_left gen A).symm
    · exact congrArg _ (runProb_dhToLR_right_link_real_eq_elgamalLR_right gen A).symm
  rw [hL]
  -- Triangle through the random branch.
  refine (Package.advantage_triangle
    (dhToLR_left.link (dhTripleReal F gen))
    (dhToLR_left.link (dhTripleRand F gen))
    (dhToLR_right.link (dhTripleReal F gen)) A).trans ?_
  refine add_le_add ?_ ?_
  · -- Left summand: SSP reduction lemma collapses to DDH advantage of `dhToLR_left`'s shift.
    exact le_of_eq <| Package.advantage_link_left_eq_advantage_shiftLeft
      dhToLR_left (dhTripleReal F gen) (dhTripleRand F gen) A
  · -- Right summand: triangle through the swap-symmetry game G₃.
    refine (Package.advantage_triangle
      (dhToLR_left.link (dhTripleRand F gen))
      (dhToLR_right.link (dhTripleRand F gen))
      (dhToLR_right.link (dhTripleReal F gen)) A).trans ?_
    have hswap :
        (dhToLR_left.link (dhTripleRand F gen)).advantage
          (dhToLR_right.link (dhTripleRand F gen)) A = 0 := by
      rw [Package.advantage_eq_of_evalDist_runProb_eq_right
        (G₁' := dhToLR_left.link (dhTripleRand F gen))
        (evalDist_runProb_dhToLR_link_rand_swap gen hg A).symm]
      exact Package.advantage_self _ _
    rw [hswap, zero_add]
    -- Final summand: SSP reduction lemma + symmetry of advantage.
    rw [Package.advantage_symm]
    exact le_of_eq <| Package.advantage_link_left_eq_advantage_shiftLeft
      dhToLR_right (dhTripleReal F gen) (dhTripleRand F gen) A

end ReductionEquivalences

end VCVio.SSP.Examples.ElGamal
