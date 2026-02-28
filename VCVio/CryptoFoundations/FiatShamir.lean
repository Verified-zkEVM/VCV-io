/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SigmaAlg
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.Coercions.Add

/-!
# Fiat-Shamir Transform

This file defines a basic version of the Fiat-Shamir transform on sigma protocols.
For simplicity we construct signature schemes rather than general proofs of knowledge.
-/

universe u v

open OracleComp OracleSpec

variable {X W PC SC Ω P : Type}
    {p : X → W → Bool} [SampleableType X] [SampleableType W]
    [DecidableEq PC] [DecidableEq Ω] [SampleableType Ω]

/-- Given a Σ-protocol and a generable relation, the Fiat-Shamir transform produces a
signature scheme. The signing algorithm commits, queries the random oracle on (message,
commitment), and then responds to the challenge.

API changes from old version:
- `unifSpec ++ₒ` → `unifSpec +`
- `query (spec := ...) () (m, c)` → `query (spec := ...) (Sum.inr (m, c))`
- `idOracle ++ₛₒ randomOracle` → explicit `QueryImpl.ofLift ... .liftTarget ... + randomOracle` -/
def FiatShamir (sigmaAlg : SigmaAlg X W PC SC Ω P p)
    (hr : GenerableRelation X W p) (M : Type) [DecidableEq M] :
    SignatureAlg (OracleComp (unifSpec + (M × PC →ₒ Ω)))
      (M := M) (PK := X) (SK := W) (S := PC × P) where
  keygen := hr.gen
  sign := fun pk sk m => do
    let (c, e) ← sigmaAlg.commit pk sk
    let r ← query (spec := unifSpec + (M × PC →ₒ Ω)) (Sum.inr (m, c))
    let s ← sigmaAlg.respond pk sk e r
    return (c, s)
  verify := fun pk m (c, s) => do
    let r' ← query (spec := unifSpec + (M × PC →ₒ Ω)) (Sum.inr (m, c))
    return sigmaAlg.verify pk c r' s
  exec comp :=
    let ro : QueryImpl (M × PC →ₒ Ω)
      (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp) := randomOracle
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp)
    StateT.run' (simulateQ (idImpl + ro) comp) ∅
  lift_probComp := monadLift
  exec_lift_probComp c := by
    let ro : QueryImpl (M × PC →ₒ Ω)
      (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp) := randomOracle
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp)
    change StateT.run' (simulateQ (idImpl + ro) (monadLift c)) ∅ = c
    rw [show simulateQ (idImpl + ro) (monadLift c) = simulateQ idImpl c by
      simpa [MonadLift.monadLift] using
        (QueryImpl.simulateQ_add_liftComp_left (impl₁' := idImpl) (impl₂' := ro) c)]
    have hid : ∀ t s, (idImpl t).run' s = query t := by
      intro t s
      rfl
    simpa using
      (StateT_run'_simulateQ_eq_self (so := idImpl) (h := hid) (oa := c)
        (s := (∅ : (M × PC →ₒ Ω).QueryCache)))

namespace FiatShamir

-- TODO: prove properties of the Fiat-Shamir transform

end FiatShamir

/-! ## Old commented code (for reference)

-- variable {ι : Type} (spec : ℕ → OracleSpec ι)
--     (X W : ℕ → Type) (p : {n : ℕ} → X n → W n → Bool)
--     (PC SC Ω P M : ℕ → Type)
--     [Π n, Inhabited (Ω n)] [Π n, DecidableEq (Ω n)]
--     [Π n, Fintype (Ω n)] [Π n, SampleableType (Ω n)]
--     [Π n, DecidableEq (PC n)] [Π n, DecidableEq (M n)]
--     [Π n, Fintype (X n)] [Π n, Inhabited (X n)] [Π n, SampleableType (X n)]
--     [Π n, Fintype (W n)] [Π n, Inhabited (W n)] [Π n, SampleableType (W n)]

-- structure GenerableRelation
--     (X W : Type) (r : X → W → Bool)
--     [SampleableType X] [SampleableType W] where
--   gen : ProbComp (X × W)
--   gen_sound (x : X) (w : W) : (x, w) ∈ gen.support → r x w
--   gen_uniform_right (x : X) : [= x | Prod.fst <$> gen] = [= x | $ᵗ X]
--   gen_uniform_left (w : W) : [= w | Prod.snd <$> gen] = [= w | $ᵗ W]
-/
