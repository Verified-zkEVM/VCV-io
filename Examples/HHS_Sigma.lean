-- /-
-- Copyright (c) 2024 Devon Tuma. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Devon Tuma
-- -/
-- import VCVio

-- import Mathlib.Data.Vector.Zip

-- /-!
-- # HHS Based Schnorr Signature

-- TODO: this should come from Fiat-Shamir instead
-- -/

-- open Mathlib OracleSpec OracleComp Sum

-- section commits

-- variable {G P M : Type} [DecidableEq M]
--     [AddCommGroup G] [AddTorsor G P] {n : ℕ}

-- def zipCommits (sk : G) (gs : Vector G n)
--     (bs : Vector Bool n) : Vector G n :=
--   Vector.zipWith (λ c b ↦ if b then c else c + sk) gs bs

-- def unzipCommits (x₀ pk : P) (zs : Vector G n)
--     (hash : Vector Bool n) : Vector P n :=
--   Vector.zipWith (λ z b ↦ if b then z +ᵥ pk else z +ᵥ x₀) zs hash

-- end commits

-- def SchnorrSigmaAlg (G P : ℕ → Type)
--     [HomogeneousSpace G P] :
--   SigmaAlg (λ _ ↦ emptySpec)
--     -- Relation is the knowledge of vectorization `sk`
--     (p := λ (x₀, pk) sk ↦ pk = sk +ᵥ x₀)
--     -- Public statement is a pair of points
--     (X := λ n ↦ P n × P n)
--     -- Witness is their vectorization
--     (W := λ n ↦ G n)
--     -- Publicly commit to a list of points
--     (PC := λ n ↦ Vector (P n) (n + 1))
--     -- Secretely commit to a list of vectors
--     (SC := λ n ↦ Vector (G n) (n + 1))
--     -- Challenge is a list of random bits
--     (Ω := λ n ↦ Vector Bool (n + 1))
--     -- Responses are a list of points
--     (P := λ n ↦ Vector (G n) (n + 1)) where
--   commit := λ n (_, pk) _ ↦ do
--     let gs ←$ᵗ Vector (G n) (n + 1)
--     let xs := gs.map (· +ᵥ pk)
--     return (xs, gs)
--   respond := λ n _ sk gs bs ↦ do
--     return gs.zipWith (λ g b ↦
--       if b then g else g + sk) bs
--   verify := λ n (x₀, pk) xs bs zs ↦
--     xs = zs.zipWith (λ z b ↦
--       if b then z +ᵥ pk else z +ᵥ x₀) bs
--   sim := λ n _ ↦ do
--     $ᵗ Vector (P n) (n + 1)
--   extract := λ n _ zs₁ _ zs₂ ↦ do
--     return zs₁[0] - zs₂[0]
--   __ := baseOracleAlg



-- def HHS_signature (G P M : Type) [DecidableEq M]
--     [AddCommGroup G] [HomogeneousSpace G P] (n : ℕ) :
--     SignatureAlg
--       (unifSpec ++ₒ ((Vector P n × M) →ₒ Vector Bool n))
--       M (P × P) G (Vector G n × Vector Bool n) where
--   keygen := λ () ↦ do
--     let x₀ ← $ᵗ P; let sk ← $ᵗ G
--     return ((x₀, sk +ᵥ x₀), sk)
--   -- Sign a message by choosing `n` random commitments, and querying the oracle on them
--   -- For each 1 bit in the resulting hash, subtract the secret key from corresponding commitment
--   sign := λ (_, pk) sk m ↦ do
--     let gs ← $ᵗ Vector G n
--     let xs : Vector P n := gs.map (· +ᵥ pk)
--     -- Note: would be better if we didn't need to do this. Outparam issue?
--     -- let j : (unifSpec ++ₒ ((Vector P n × M) →ₒ Vector Bool n)).ι := inr ()
--     let bs : Vector Bool n ← query (inr ()) (xs, m)
--     let zs : Vector G n := zipCommits sk gs bs
--     return (zs, bs)
--   -- Verify a signature by adding each commit to the appropriate point in the public key
--   -- Signatures are valid if the result of hashing this matches the original hash
--   verify := λ ⟨x₀, pk⟩ m (zs, bs) ↦ do
--     let xs : Vector P n := unzipCommits x₀ pk zs bs
--     -- let j : (unifSpec ++ ((Vector P n × M) →ₒ Vector Bool n)).ι := inr ()
--     let bs' : Vector Bool n ← query (inr ()) (xs, m)
--     return (bs' = bs)
--   -- Treat the second oracle as a random oracle
--   baseSimOracle := SimOracle.equivState
--     (idOracle ++ₛₒ randOracle) (Equiv.punitProd _)
--   init_state := ∅
