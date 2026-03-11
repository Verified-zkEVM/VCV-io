/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.Coercions.Add
import VCVio.ProgramLogic.Tactics

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
commitment), and then responds to the challenge. -/
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

/-- Structural bound that counts only random-oracle queries in a Fiat-Shamir
EUF-CMA adversary. Uniform-sampling and signing-oracle queries are unrestricted. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × PC →ₒ Ω)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => True
      | .inl (.inr _) => 0 < b)
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => b
      | .inl (.inr _) => b - 1)

/-- Reciprocal of the finite challenge-space size. -/
noncomputable def challengeSpaceInv (challenge : Type) [Fintype challenge] : ENNReal :=
  (Fintype.card challenge : ENNReal)⁻¹

omit [DecidableEq P] [DecidableEq Ω] in
/-- Completeness of the Fiat-Shamir signature scheme follows from completeness of the
underlying Σ-protocol. -/
theorem perfectlyCorrect (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete (FiatShamir σ hr M) := by
  intro msg
  classical
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
    show StateT.run' (simulateQ (idImpl + ro) (do
        let (pk, sk) ← (FiatShamir σ hr M).keygen
        let sig ← (FiatShamir σ hr M).sign pk sk msg
        (FiatShamir σ hr M).verify pk msg sig)) ∅ = _
    dsimp only [FiatShamir]
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_query,
      QueryImpl.add_apply_inr,
      OracleQuery.cont_query, OracleQuery.input_query, id_map]
    have hpeel : ∀ {α β : Type} (oa : ProbComp α)
        (rest : α → StateT ((M × PC →ₒ Ω).QueryCache) ProbComp β)
        (s : (M × PC →ₒ Ω).QueryCache),
        (simulateQ (idImpl + ro) (liftM oa) >>= rest).run' s =
          oa >>= fun x => (rest x).run' s := by
      intro α β oa rest s
      show Prod.fst <$> ((simulateQ (idImpl + ro) (liftM oa) >>= rest).run s) =
        oa >>= fun x => Prod.fst <$> (rest x).run s
      rw [StateT.run_bind, hrunLift]
      simp [map_bind]
    simp_rw [hpeel]
    have hlift : ∀ {α : Type} (x : ProbComp α) (s : (M × PC →ₒ Ω).QueryCache),
        (liftM x : StateT _ ProbComp α).run s = x >>= fun a => pure (a, s) := by
      intro α x s
      simp only [liftM, MonadLiftT.monadLift,
        show OracleComp.liftComp x unifSpec = x from monadLift_eq_self x,
        MonadLift.monadLift, StateT.run_lift]
    have hmod : ∀ {α : Type}
        (f : (M × PC →ₒ Ω).QueryCache → α × (M × PC →ₒ Ω).QueryCache)
        (s : (M × PC →ₒ Ω).QueryCache),
        (modifyGet f : StateT _ ProbComp α).run s = pure (f s) := by
      intro α f s
      simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
    have hro_miss : ∀ {β : Type} (q : M × PC)
        (rest : Ω → StateT ((M × PC →ₒ Ω).QueryCache) ProbComp β),
        (ro q >>= rest).run' ∅ =
          $ᵗ Ω >>= fun r =>
            (rest r).run' ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r) := by
      intro β q rest
      show Prod.fst <$> ((ro q >>= rest).run ∅) =
        $ᵗ Ω >>= fun r =>
          Prod.fst <$> (rest r).run ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r)
      simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
        StateT.run_get, pure_bind, uniformSampleImpl, bind_assoc, map_bind,
        liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, StateT.run_lift, hmod]
    simp only [bind_assoc, pure_bind]
    simp_rw [hpeel]
    simp_rw [hro_miss]
    simp_rw [hpeel]
    have hro_hit : ∀ {β : Type} (q : M × PC) (r : Ω)
        (rest : Ω → StateT ((M × PC →ₒ Ω).QueryCache) ProbComp β),
        (ro q >>= rest).run' ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r) =
          (rest r).run' ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r) := by
      intro β q r rest
      show Prod.fst <$> ((ro q >>= rest).run
          ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r)) =
        Prod.fst <$> (rest r).run
          ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r)
      rw [StateT.run_bind]
      simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
        StateT.run_get, pure_bind, QueryCache.cacheQuery_self, StateT.run_pure]
    simp_rw [hro_hit]
    have hpure_run' : ∀ {α : Type} (a : α) (s : (M × PC →ₒ Ω).QueryCache),
        (pure a : StateT _ ProbComp α).run' s = (pure a : ProbComp α) := by
      intro α a s
      change Prod.fst <$> (pure (a, s) : ProbComp _) = pure a
      simp [map_pure]
    simp_rw [hpure_run']]
  qvcgen_step
  qvcgen_step using (fun x => OracleComp.ProgramLogic.propInd (x ∈ support hr.gen))
  · simpa [OracleComp.ProgramLogic.propInd] using
      OracleComp.ProgramLogic.triple_support (oa := hr.gen)
  · intro x
    rcases x with ⟨pk, sk⟩
    by_cases hx : (pk, sk) ∈ support hr.gen
    · have hrel : p pk sk = true := hr.gen_sound pk sk hx
      simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_probOutput_eq_one
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Ω
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (x := true) (h := by simpa using hc pk sk hrel))
    · simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_zero
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Ω
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (post := fun y => if y = true then 1 else 0))

/-- Pointcheval-Stern style Fiat-Shamir reduction statement.

To obtain a meaningful EUF-CMA theorem we need:
* special soundness, to extract a witness from a successful fork;
* an HVZK simulator for the underlying Σ-protocol, to model signing without the witness;
* a structural bound on hash-oracle queries.

The conclusion is stated as the existence of a witness-finding reduction rather
than a fully explicit adversary, since the concrete reduction is not yet
implemented in this file. -/
theorem euf_cma_bound
    (hss : σ.SpeciallySound)
    [Fintype Ω]
    (simTranscript : X → ProbComp (PC × Ω × P))
    (hhvzk : σ.HVZK simTranscript)
    (adv : SignatureAlg.unforgeableAdv (FiatShamir σ hr M))
    (qBound : ℕ)
    (hQ : ∀ pk, hashQueryBound (M := M) (PC := PC) (Ω := Ω)
      (S' := PC × P) (oa := adv.main pk) qBound) :
    ∃ reduction : X → ProbComp W,
      (adv.advantage *
          (adv.advantage / (qBound + 1 : ENNReal) - challengeSpaceInv Ω)) ≤
        Pr[= true | hardRelationExp (r := p) reduction] := by
  sorry

end FiatShamir
