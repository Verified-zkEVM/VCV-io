/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio
import Mathlib.Data.Vector.Zip

/-!
# HHS Based Schnorr Signature

TODO: remove fully for sigma alg version
-/

-- def statelessSimOracle {ι : Type} {spec : OracleSpec}

open OracleSpec OracleComp

-- open OracleSpec OracleComp Sum

-- section commits

-- variable {G P M : Type} [DecidableEq M]
--     [AddCommGroup G] [AddTorsor G P] {n : ℕ}

-- def zipCommits (sk : G) (gs : Vector G n)
--     (bs : Vector Bool n) : Vector G n :=
--   Vector.zipWith (λ c b ↦
--     if b then c else c + sk) gs bs

-- def unzipCommits (x₀ pk : P) (zs : Vector G n)
--     (hash : Vector Bool n) : Vector P n :=
--   Vector.zipWith (λ z b ↦
--     if b then z +ᵥ pk else z +ᵥ x₀) zs hash

-- end commits

-- def HHS_signature (G P M : Type) [DecidableEq M] [SampleableType P] [SampleableType G]
--     [AddCommGroup G] [AddTorsor G P] (n : ℕ) :
--     SignatureAlg
--       (unifSpec ++ₒ ((Vector P n × M) →ₒ Vector Bool n))
--       ProbComp
--       M (P × P) G (Vector G n × Vector Bool n) where
--   keygen := do
--     let x₀ ← $ᵗ P; let sk ← $ᵗ G
--     return ((x₀, sk +ᵥ x₀), sk)
--   -- Sign a message by choosing `n` random commitments, and querying the oracle on them
--   -- For each 1 bit in the resulting hash, subtract the secret key from corresponding commitment
--   sign := λ (_, pk) sk m ↦ do
--     let gs : List G ← ($ᵗ G).replicate n
--     let xs : List P := gs.map (· +ᵥ pk)
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
--   impl := sorry
--   exec_as_probComp := sorry

  -- Treat the second oracle as a random oracle
  -- baseSimOracle := SimOracle.equivState
  --   (idOracle ++ₛₒ randOracle) (Equiv.punitProd _)
  -- init_state := ∅

-- namespace HHS_signature

-- variable {G P M : Type} [DecidableEq M]
--     [AddCommGroup G] [HomogeneousSpace G P] {n : ℕ}

-- variable [(j : (unifSpec ++ (Unit →ₒ Vector Bool n)).ι) →
--   SampleableType ((unifSpec ++ (Unit →ₒ Vector Bool n)).Range j)]

-- def mockSignOracle  (x₀ pk : P) :
--     let randSpec := (Vector P n × M) →ₒ Vector Bool n
--     let sigSpec := M →ₒ (Vector G n × Vector Bool n)
--     ((unifSpec ++ₒ randSpec) ++ₒ sigSpec)
--       →[Bool × QueryCache randSpec]ₛₒ
--         (unifSpec ++ₒ (Unit →ₒ Vector Bool n)) :=
--   λ i ↦ match i with
--   | inl (inl k) => λ () (crpt, cache) ↦
--       (·, crpt, cache) <$> query (inl k) ()
--   | inl (inr ()) => λ (xs, m) (crpt, cache) ↦ match cache () (xs, m) with
--     | none => do
--         let bs : Vector Bool n ← query (inr ()) ()
--         return (bs, crpt, cache.cacheQuery () (xs, m) bs)
--     | some bs => return (bs, crpt, cache)
--   | inr () => λ m (crpt, cache) ↦ do
--       let zs ← $ᵗ (Vector G n)
--       let bs ← query (inr ()) ()
--       let xs := unzipCommits x₀ pk zs bs
--       -- already exists in cache
--       let bad := (cache () (xs, m)).isSome
--       let cache' := (cache.cacheQuery () (xs, m) bs)
--       return ((zs, bs), crpt || bad, cache')

-- def forkReduction (adv : (HHS_signature G P M n).unforgeableAdv) :
--     ForkAdv (unifSpec ++ₒ (Unit →ₒ Vector Bool n)) (P × P)
--       ((M × Vector G n × Vector Bool n) × Bool ×
--         QueryCache ((Vector P n × M) →ₒ Vector Bool n)) (inr ()) where
--   run := λ (x₀, pk) ↦ simulate (mockSignOracle x₀ pk)
--     (false, ∅) (adv.run (x₀, pk))
--   chooseFork := λ (x₀, pk) ↦ sorry
--   queryBound := sorry
--   activeOracles := sorry

-- -- def vectorizationReduction (adv : (HHS_signature G P M n).unforgeableAdv) :
-- --     HomogeneousSpace.vectorizationAdv G P where
-- --   run := λ (x₀, pk) ↦ simulate' unifOracle () <| do
-- --     let z ← (fork (forkReduction adv)).run (x₀, pk)
-- --     match z with
-- --     | some (((m, σ), crpt, cache), z) => sorry
-- --     | none => return default
-- --   queryBound := sorry
-- --   activeOracles := sorry

-- end HHS_signature
