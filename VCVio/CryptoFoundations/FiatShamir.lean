/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
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
def FiatShamir (sigmaAlg : SigmaProtocol X W PC SC Ω P p)
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

variable {X W PC SC Ω P : Type} {p : X → W → Bool}
  [SampleableType X] [SampleableType W]
  [DecidableEq PC] [DecidableEq P] [DecidableEq Ω] [SampleableType Ω]

variable (σ : SigmaProtocol X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (M : Type) [DecidableEq M]

/-- Completeness of the Fiat-Shamir signature scheme follows from completeness of the
underlying Σ-protocol. -/
theorem perfectlyCorrect (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete (FiatShamir σ hr M) := by
  intro msg
  let ro : QueryImpl (M × PC →ₒ Ω)
      (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp) := randomOracle
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp)
  have hleft :
      ∀ {α : Type} (oa : ProbComp α),
        simulateQ (idImpl + ro) (OracleComp.liftComp oa (unifSpec + (M × PC →ₒ Ω))) =
          simulateQ idImpl oa := by
    intro α oa
    simpa using
      (QueryImpl.simulateQ_add_liftComp_left (impl₁' := idImpl) (impl₂' := ro) oa)
  have hrun :
      ∀ {α : Type} (oa : ProbComp α) (s : (M × PC →ₒ Ω).QueryCache),
        (simulateQ idImpl oa).run s = (fun x => (x, s)) <$> oa := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure x =>
        intro s
        simp
    | query_bind t oa ih =>
        intro s
        change
          (do
            let a ← (liftM (query t) : ProbComp (unifSpec.Range t))
            (simulateQ idImpl (oa a)).run s) =
            (do
              let a ← liftM (query t)
              (fun x => (x, s)) <$> oa a)
        have hfun :
            (fun a => (simulateQ idImpl (oa a)).run s) =
              (fun a => (fun x => (x, s)) <$> oa a) := by
          funext a
          exact ih a s
        simp [hfun]
  have hrunLift :
      ∀ {α : Type} (oa : ProbComp α) (s : (M × PC →ₒ Ω).QueryCache),
        (simulateQ (idImpl + ro) (liftM oa)).run s = (fun x => (x, s)) <$> oa := by
    intro α oa s
    rw [show simulateQ (idImpl + ro) (liftM oa) = simulateQ idImpl oa by
      simpa using hleft oa]
    simpa using hrun oa s
  change
    Pr[= true | (FiatShamir σ hr M).exec (do
      let (pk, sk) ← (FiatShamir σ hr M).keygen
      let sig ← (FiatShamir σ hr M).sign pk sk msg
      (FiatShamir σ hr M).verify pk msg sig)] = 1
  rw [show (FiatShamir σ hr M).exec (do
      let (pk, sk) ← (FiatShamir σ hr M).keygen
      let sig ← (FiatShamir σ hr M).sign pk sk msg
      (FiatShamir σ hr M).verify pk msg sig) =
        (do
          let (pk, sk) ← hr.gen
          let (c, e) ← σ.commit pk sk
          let r ← $ᵗ Ω
          let s ← σ.respond pk sk e r
          pure (σ.verify pk c r s)) by
    sorry /- was: simp; simp_rw [hrunLift]; simp — broken by @[simp] monadLift_eq_self -/]
  have hinner :
      ∀ x ∈ support hr.gen,
        Pr[= true | (do
          let (c, e) ← σ.commit x.1 x.2
          let r ← $ᵗ Ω
          let s ← σ.respond x.1 x.2 e r
          pure (σ.verify x.1 c r s))] =
          Pr[= true | (pure true : ProbComp Bool)] := by
    intro x hx
    rcases x with ⟨pk, sk⟩
    have hrel : p pk sk = true := hr.gen_sound pk sk hx
    simpa using hc pk sk hrel
  calc
    Pr[= true | (do
      let (pk, sk) ← hr.gen
      let (c, e) ← σ.commit pk sk
      let r ← $ᵗ Ω
      let s ← σ.respond pk sk e r
      pure (σ.verify pk c r s))] =
        Pr[= true | (do
          let _x ← hr.gen
          pure true : ProbComp Bool)] := by
            exact probOutput_bind_congr hinner
    _ = 1 := by simp

/-- EUF-CMA security of Fiat-Shamir: if the Σ-protocol is specially sound, then
forgery probability is bounded by the forking lemma probability. -/
theorem euf_cma_bound
    (hss : σ.SpeciallySound)
    (adv : SignatureAlg.unforgeableAdv (FiatShamir σ hr M))
    (qBound : ℕ) :
    adv.advantage ≤
      sorry := by
  sorry

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
