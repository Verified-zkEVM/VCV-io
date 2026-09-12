/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign

/-!
# GPV #188 EUF-CMA: hypothesis-consistency witness

The GPV hash-and-sign EUF-CMA bounds (`GPVHashAndSign.forgery_yields_collision_or_exact_match`
and the `euf_cma_*` corollaries) are stated under side conditions — PSF correctness and regularity,
a never-failing trapdoor sampler, the random-oracle "forger queries its forgery point" convention
(`ForgesQueriedPoint`), and a query-count bound (`signHashQueryBound`).  A conditional theorem says
nothing if its hypotheses are jointly uninhabitable: this file rules that out with a concrete
instance for which every side condition holds simultaneously.  This is a **logical consistency
(inhabitance) witness only** — the one-point key space and two-point domain carry no
quantitative security content.

The witness is the canonical bijective PSF over `Bool` with `PK = SK = Unit`: `eval` is the
identity, `trapdoorSample` returns its argument (the inverse of the identity), and the shortness
predicate is constantly `true`.  The adversary `adv` queries the random oracle once at a fixed point
and then forges at that same point, so its forgery key is constant and always cached — witnessing
`ForgesQueriedPoint`.

* `bijPSF_correct` / `bijPSF_regularity` — the PSF-side conditions.
* `bijPSF_neverFail` — the trapdoor sampler never fails.
* `bijPSF_hForge` — the forger queries its forgery point, for *every* domain sampler.
* `adv_signHashQueryBound` — the adversary makes `0` signing and `1` random-oracle queries.
* `gpv188_hyps_inhabited` — all five side conditions hold for the single instance
  `(bijPSF, hr, adv)`, in exactly the shape the headline bounds consume them.
-/

public section

open OracleComp OracleSpec

namespace Examples.GPVNonVacuity

/-- The canonical bijective PSF over `Bool`: `eval` is the identity, `trapdoorSample` returns its
argument (the inverse), and shortness is constantly `true`. -/
def bijPSF : PreimageSampleableFunction Unit Unit Bool Bool where
  eval := fun _ d => d
  trapdoorSample := fun _ _ r => pure r
  isShort := fun _ => true

/-- The trivial generable relation on `Unit` keys. -/
def hr : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((), ())
  gen_sound := by intro x w _; rfl

/-- A query-then-forge adversary: it queries the random oracle once at `((), ())` and then forges
at that same `(salt, message) = ((), ())`, so its forgery key is the constant `((), ())`. -/
noncomputable def adv :
    SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Unit × Unit →ₒ Bool)))
        bijPSF hr Unit Unit) where
  main := fun _pk => do
    let _c ← (OracleComp.lift (OracleSpec.query
      (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
      (.inl (.inr ((), ())))))
    pure ((), ((), false))

/-- The domain sampler witnessing regularity (uniform on `Bool`). -/
noncomputable def domainSample : Unit → ProbComp Bool := fun _ => ($ᵗ Bool)

/-- The forger queries its forgery point, for every domain sampler: for every run in the support,
the cache at the (constant) forged key `((), ())` is non-`none`.  The single random-oracle query
`adv` makes is at exactly that point, and a programmed read step always leaves its point cached
(`GPVHashAndSign.progGameRunImplNoRecFlagFresh_read_caches`) — on a hit the entry is preserved, on
a miss the handler programs it.  This is the `∀ ds` shape consumed by `euf_cma_split_bound` and
`euf_cma_collision_bound`. -/
theorem bijPSF_hForge (ds : Unit → ProbComp Bool) :
    GPVHashAndSign.ForgesQueriedPoint bijPSF hr Unit Unit adv ds := by
  unfold GPVHashAndSign.ForgesQueriedPoint
  intro pk z hz
  rw [show adv.main pk = (liftM (OracleSpec.query
      (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
      (.inl (.inr ((), ()))))) >>= fun _ => pure ((), ((), false)) from rfl] at hz
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, smid⟩, hmid, hrest⟩ := hz
  have hcache : smid.1.1 ((), ()) ≠ none :=
    GPVHashAndSign.progGameRunImplNoRecFlagFresh_read_caches bijPSF Unit Unit ds pk ((), ())
      _ _ hmid
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  subst hrest
  exact hcache

/-- The witness adversary makes exactly one random-oracle query and zero signing queries. -/
theorem adv_signHashQueryBound (pk : Unit) :
    GPVHashAndSign.signHashQueryBound Unit Unit (adv.main pk) 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [show adv.main pk = (liftM (OracleSpec.query
        (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
        (.inl (.inr ((), ()))))) >>= fun _ => pure ((), ((), false)) from rfl]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by decide), fun _ => trivial⟩
  · rw [show adv.main pk = (liftM (OracleSpec.query
        (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
        (.inl (.inr ((), ()))))) >>= fun _ => pure ((), ((), false)) from rfl]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-- The witness PSF is correct: its trapdoor sampler is the identity, so every preimage hashes back
to its target and passes the (constantly true) shortness predicate. -/
theorem bijPSF_correct : bijPSF.Correct := by
  intro pk sk t x hx
  simp only [bijPSF, support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨rfl, rfl⟩

/-- The witness PSF has a never-failing trapdoor sampler: at every key pair and target it is the
deterministic `pure`, which has no failure branch. -/
theorem bijPSF_neverFail :
    ∀ (pk sk : Unit), (pk, sk) ∈ support hr.gen →
      ∀ c : Bool, NeverFail (bijPSF.trapdoorSample pk sk c) := by
  intro pk sk _ c
  change NeverFail (pure c : ProbComp Bool)
  infer_instance

/-- The witness PSF satisfies GPV regularity with `domainSample = $ᵗ Bool`: forward-sampling a short
preimage and hashing it forward is identical to sampling a uniform target and inverting it. -/
theorem bijPSF_regularity : bijPSF.Regularity := by
  refine ⟨domainSample, fun pk sk => ?_⟩
  simp only [bijPSF, domainSample, pure_bind]

/-- **Consistency (inhabitance) witness for the GPV #188 headline hypotheses.** For the concrete
bijective PSF, the generable relation `hr`, and the query-then-forge adversary `adv`, all the
standard GPV side conditions hold simultaneously: the forger queries its forgery point for every
domain sampler (`ForgesQueriedPoint`), the adversary makes `0` signing and `1` random-oracle queries
(`signHashQueryBound`), the PSF is correct (`Correct`), the trapdoor sampler never fails
(`NeverFail`), and the PSF is regular (`Regularity`).  Each conjunct is stated in the exact shape
the headline bounds `GPVHashAndSign.euf_cma_split_bound` and
`GPVHashAndSign.euf_cma_collision_bound` consume — in particular `ForgesQueriedPoint` universally
quantified over the domain sampler — so their hypothesis conjunction is inhabitable.  This witness
carries no quantitative security content. -/
theorem gpv188_hyps_inhabited :
    (∀ ds : Unit → ProbComp Bool,
      GPVHashAndSign.ForgesQueriedPoint bijPSF hr Unit Unit adv ds) ∧
    (∀ pk : Unit, GPVHashAndSign.signHashQueryBound Unit Unit (adv.main pk) 0 1) ∧
    bijPSF.Correct ∧
    (∀ (pk sk : Unit), (pk, sk) ∈ support hr.gen →
      ∀ c : Bool, NeverFail (bijPSF.trapdoorSample pk sk c)) ∧
    bijPSF.Regularity :=
  ⟨bijPSF_hForge, adv_signHashQueryBound, bijPSF_correct, bijPSF_neverFail, bijPSF_regularity⟩

end Examples.GPVNonVacuity
