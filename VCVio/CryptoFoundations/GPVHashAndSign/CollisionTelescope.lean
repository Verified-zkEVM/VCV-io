/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.Basic

/-! # GPV Hash-and-Sign: The Salt-Collision Telescope

The proof decomposition overview, the salt-averaged collision telescope over the
combined draw-then-query step, the salt-collision coupling at hash-only
granularity, and the salt-inclusive identical-until-bad coupling primitives.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! ## Proof Decomposition

The EUF-CMA security proof proceeds by a game-hopping argument:

**Game 0**: The real EUF-CMA experiment with a lazy random oracle and the honest
signing oracle (trapdoor sampler).

**Game 1**: Replace signing with "sign-then-hash": for each signing query on message `m`,
sample a short preimage `s ← D_short`, set `c := psf.eval pk s`, program the RO at
`(r, m) := c`, and return `(r, s)`. This is indistinguishable from Game 0 when the PSF
sampler is correct (the output distribution conditioned on the target is the same).

**Bad event**: A fresh signing salt lands on a `(salt, message)` pair already recorded in the
random oracle, by a prior signing query or an adversary hash query. Under the birthday bound,
this happens with probability at most `(q_S + q_H)² / (2 · |Salt|)` (`collisionBound`).

**Game 2 (reduction)**: The simulator programs the random oracle with hidden short preimages.
If the adversary forges on a fresh `(salt, message)` pair and the forged short preimage differs
from the simulator's hidden programmed preimage at that point, the pair forms a collision under
`psf.eval`.

The exact-match branch, where the forgery reproduces the simulator's programmed preimage, is a
separate one-way/min-entropy obligation and is intentionally not encoded in the collision game
below.
-/

/-- The collision-branch GPV reduction adversary. Given a public key `pk`,
the reduction internally simulates the CMA experiment for the adversary:

1. Program a lazy random oracle, storing for each entry the hidden short preimage used to
   define that entry.
2. Answer signing queries using the sign-then-hash strategy: sample a short preimage
   `s` via `trapdoorSample`, compute `c = psf.eval pk s`, and program the RO at
   `(r, msg) := c`. Return `(r, s)` as the signature.
3. Run the adversary and, on a successful fresh forgery, return the simulator's hidden
   programmed preimage together with the forged preimage as a candidate collision.

The key insight is that in the sign-then-hash game, the reduction controls the entire
RO table. If the adversary forges on a fresh `(r*, msg*)` pair, the RO value at that
point was set by the reduction, so the hidden programmed preimage and the forged preimage
land at the same image under `psf.eval`.

The detailed construction simulates the adversary's oracle interactions by maintaining
a programmable RO state, using PSF correctness to ensure consistency. -/
@[expose] noncomputable def reduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    CollisionAdversary (PK := PK) (Domain := Domain) :=
  fun pk => do
    -- The simulation state threads the lazy random-oracle cache together with a *hidden
    -- preimage table* recording, for each programmed `(salt, message)` entry, the short
    -- preimage `s` used to define `psf.eval pk s` as the random-oracle value at that point.
    let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
    -- Random-oracle handler: on a cache hit reuse the recorded value; on a miss
    -- forward-sample a short preimage `s ← domainSample pk`, set the value to `psf.eval pk s`,
    -- and record `s` in the hidden table at the queried point.
    let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
      fun t => do
        let st ← get
        match st.1 t with
        | some v => pure v
        | none => do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
            pure v
    -- Uniform-sampling handler: answer uniform queries by drawing from the ambient `ProbComp`.
    let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
      fun t => (unifSpec.query t : ProbComp _)
    -- Signing handler (sign-then-hash): draw a fresh salt `r`, forward-sample a short preimage
    -- `s ← domainSample pk`, program the random oracle at `(r, msg) := psf.eval pk s`, record the
    -- hidden preimage, and return the signature `(r, s)`.
    let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
      fun msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let s ← (domainSample pk : ProbComp Domain)
        let v := psf.eval pk s
        let st ← get
        set ((st.1.cacheQuery (r, msg) v,
          fun t' => if t' = (r, msg) then some s else st.2 t') : State)
        pure (r, s)
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
    -- Run the adversary under the simulated oracle stack, then extract a collision candidate.
    let ((msgStar, (rStar, sStar)), st) ←
      (simulateQ impl (adv.main pk)).run (∅, fun _ => none)
    -- On the forgery `(msgStar, (rStar, sStar))`, look up the hidden programmed preimage at the
    -- forged point. If present, it and the forged preimage `sStar` share the image
    -- `psf.eval pk sStar` (the random-oracle value the reduction programmed there), forming a
    -- collision candidate. Otherwise fall back to the forged preimage itself.
    match st.2 (rStar, msgStar) with
    | some sHidden => pure (sHidden, sStar)
    | none => pure (sStar, sStar)

/-- The salt-collision birthday bound, in the closed form `(qSign + qHash)² / (2 · |Salt|)`.

For `qSign` signing queries and `qHash` random-oracle queries, with salts drawn uniformly from a
set of size `|Salt|`, this bounds the probability that a fresh signing salt collides with any
previously recorded random-oracle input (a prior signing salt or an adversary hash query). What
the telescope actually establishes is the exact union sum `∑_{j < qSign} (j + qHash) / |Salt|`
(`sum_range_div_card_le_collisionBound`): the `j`-th fresh draw is compared against at most
`j + qHash` recorded entries, and `∑_{j < qSign} (j + qHash) = qSign·(qSign-1)/2 + qSign·qHash`
is at most `(qSign + qHash)² / 2`. This closed form is the constant the headline bounds state.

Relation to the literature: GPV08 (Proposition 6.2) only sketches the same-message salt reuse
term `Q_sign² / 2^k`; the salt-vs-hash-query accounting is the `Q_s · (C_s + Q_H) / 2^k` term of
[FGdG+25] Theorem 1, recorded in the umbrella module docstring. The closed form here is looser
than the union sum by the `qHash² / 2` term, which dominates when `qHash ≫ qSign`; at Falcon's
symmetric budget below the difference is immaterial.

For Falcon with 40-byte salts (`|Salt| = 2^320`) and `qSign, qHash ≤ 2^64`:
  `collisionBound (Bytes 40) (2^64) (2^64) = 2^130 / (2 · 2^320) = 2^{-191}`. -/
@[expose] noncomputable def collisionBound (qSign qHash : ℕ) : ENNReal :=
  ((qSign + qHash : ℕ) : ENNReal) ^ 2 / (2 * Fintype.card Salt)

open scoped Classical in
omit [DecidableEq Salt] in
/-- A single uniform salt draw lands in a fixed cache `cache ⊆ Salt` with probability exactly
`|cache| / |Salt|`.

This is the per-draw building block of the GPV salt-collision union bound: each fresh salt is
sampled uniformly and independently, so the chance it hits any of the previously recorded
random-oracle inputs is the size of that recorded set over the size of the salt space. -/
lemma probEvent_mem_uniformSample (cache : Finset Salt) :
    Pr[(· ∈ cache) | ($ᵗ Salt)] = cache.card / Fintype.card Salt := by
  rw [probEvent_uniformSample]
  congr 1
  simp

omit [DecidableEq Salt] [SampleableType Salt] in
/-- Arithmetic core of the GPV salt-collision birthday bound.

Summing the per-draw collision probabilities for `qSign` signing queries, where the `j`-th
fresh salt is compared against the at most `j + qHash` recorded random-oracle inputs (the `j`
prior signing salts and the up to `qHash` adversary hash queries), gives the running total
`∑_{j < qSign} (j + qHash) / |Salt|`. The exact sum
`∑_{j < qSign} (j + qHash) = qSign·(qSign-1)/2 + qSign·qHash` is at most `(qSign + qHash)² / 2`,
so the union bound is dominated by `collisionBound`. -/
lemma sum_range_div_card_le_collisionBound (qSign qHash : ℕ) :
    (∑ j ∈ Finset.range qSign, ((j + qHash : ℕ) : ℝ≥0∞) / Fintype.card Salt)
      ≤ collisionBound Salt qSign qHash := by
  unfold collisionBound
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hsum : (∑ j ∈ Finset.range qSign, ((j + qHash : ℕ) : ℝ≥0∞))
      = ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) := by rw [Nat.cast_sum]
  rw [hsum]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc]
  gcongr
  have hnat : (∑ j ∈ Finset.range qSign, (j + qHash)) * 2 ≤ (qSign + qHash) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range,
      smul_eq_mul, add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self qSign).two_dvd]
    rcases Nat.eq_zero_or_pos qSign with h | h
    · simp [h]
    · nlinarith [Nat.sub_le qSign 1]
  have hcast : ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) * 2
      ≤ (((qSign + qHash : ℕ) : ℝ≥0∞)) ^ 2 := by
    have h2 := (Nat.cast_le (α := ℝ≥0∞)).2 hnat
    push_cast at h2 ⊢
    convert h2 using 2
  calc ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞)
      = ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) * 2 * 2⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    _ ≤ ((qSign + qHash : ℕ) : ℝ≥0∞) ^ 2 * 2⁻¹ := by gcongr

open scoped Classical in
omit [DecidableEq Salt] in
/-- The GPV salt-collision union bound (GPV08, Proposition 6.2), as a uniform-draw-hits-cache
estimate.

If the random-oracle cache seen by the `j`-th signing query has size at most `j + qHash` (the `j`
prior signing salts plus the up to `qHash` adversary hash queries already recorded), then the
total probability that some fresh salt collides with a previously recorded entry is bounded by
`collisionBound`. The hypothesis `hcache` supplies the per-draw cache sizes `c j` together with
the bound `c j ≤ j + qHash`; the conclusion is the union bound over the `qSign` independent
uniform draws.

This is the real salt-collision event of the GPV proof (a fresh uniform draw hitting the
recorded random-oracle inputs), distinct from a hash-*output* collision over `|Range|`. -/
lemma probEvent_salt_collision_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    (∑ j ∈ Finset.range qSign, Pr[(· ∈ c j) | ($ᵗ Salt)]) ≤ collisionBound Salt qSign qHash := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_range_div_card_le_collisionBound Salt qSign qHash)
  intro j _
  rw [probEvent_mem_uniformSample]
  gcongr
  exact_mod_cast hcache j

/-! ## Salt-averaged collision telescope (the combined draw-then-query step)

A per-query `withProgramming` union framework cannot see the GPV salt averaging: the programming bad
flag fires deterministically on a *fixed* query input `t = (r, m)`, while the collision randomness
lives in the fresh salt `r` drawn *inside* the signing oracle, one step *before* the random-oracle
query is issued. The right granularity is therefore a **combined "draw salt `r`, then check `r`
against the recorded inputs" step**, whose firing probability, *integrated over the uniform salt
draw*, is `card cache / |Salt|`.

`saltSeq` is exactly this combined-step process abstracted away from the oracle plumbing: it
draws `qSign` fresh salts in sequence and reports whether any draw `r_j` lands in the recorded
set `c j` seen by the `j`-th signing query. `probEvent_saltSeq_le` telescopes the per-draw
collision probabilities (each a `probEvent_mem_uniformSample` instance) into the running sum
`∑_{j < qSign} card (c j) / |Salt|`, and `probEvent_saltSeq_le_collisionBound` finishes with the
Gauss-sum estimate `sum_range_div_card_le_collisionBound`. This is the salt-AVERAGED step bound
matching the granularity of the fresh salt draw. -/

open Classical in
omit [DecidableEq Salt] in
/-- The combined draw-then-collision-check process underlying the GPV salt-collision union bound.

`saltSeq c n` draws `n` fresh uniform salts in sequence; the `j`-th draw `r_j` is checked for
membership in the recorded random-oracle input set `c j` (the salts and hash inputs seen by the
`j`-th signing query). It returns `true` iff some draw collides with its recorded set. This is the
salt-averaged abstraction of "draw a fresh signing salt, then query the random oracle at it":
firing is integrated over the fresh draw rather than evaluated at a fixed query input. -/
@[expose] noncomputable def saltSeq (c : ℕ → Finset Salt) : (n : ℕ) → ProbComp Bool
  | 0 => pure false
  | (n + 1) => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let rest ← saltSeq c n
      pure ((decide (r ∈ c n)) || rest)

/-- **Salt-averaged collision telescope.** The probability that the combined draw-then-check
process `saltSeq c n` ever reports a collision is bounded by the running sum of per-draw
collision probabilities `∑_{j < n} card (c j) / |Salt|`.

This is the salt-AVERAGED per-step bound: the head draw `r ← $ᵗ Salt` contributes
`card (c n) / |Salt|` (one `probEvent_mem_uniformSample` instance, integrated over the fresh salt),
and the remaining `n` draws contribute the inductive tail. The union is assembled by
`probEvent_bind_le_add` on the monotone Boolean disjunction. Unlike a fixed-`t` `withProgramming`
step (which fires deterministically and cannot be capped below `1`), every step here is averaged
over its own fresh salt draw, so the small `card / |Salt|` cap is honest. -/
theorem probEvent_saltSeq_le (c : ℕ → Finset Salt) (n : ℕ) :
    Pr[(· = true) | saltSeq (Salt := Salt) c n]
      ≤ ∑ j ∈ Finset.range n, ((c j).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
  classical
  induction n with
  | zero => simp [saltSeq]
  | succ n ih =>
      rw [probEvent_congr' (q := fun y : Bool => ¬ y = false)
            (oa' := saltSeq (Salt := Salt) c (n + 1)) (fun b _ => by cases b <;> simp) rfl]
      rw [saltSeq, Finset.sum_range_succ, add_comm]
      refine probEvent_bind_le_add (m := ProbComp)
        (p := fun r => r ∉ c n) (q := fun b : Bool => b = false)
        (ε₁ := ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        (ε₂ := ∑ j ∈ Finset.range n, ((c j).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        ?_ ?_
      · simp only [not_not]
        rw [probEvent_uniformSample]
        simp
      · intro r _ hr
        simp only [Bool.not_eq_false]
        rw [decide_eq_false hr]
        simp only [Bool.false_or]
        rw [bind_pure]
        exact ih

/-- **Salt-averaged collision telescope, finished against `collisionBound`.** When the recorded
input set seen by the `j`-th signing query has size at most `j + qHash` (the `j` prior signing
salts plus the up to `qHash` adversary hash queries), the combined draw-then-check process over
`qSign` signing queries reports a collision with probability at most `collisionBound Salt qSign
qHash`.

This chains `probEvent_saltSeq_le` with the Gauss-sum estimate
`sum_range_div_card_le_collisionBound`. It is the salt-averaged collision bound stated directly on
the fresh-salt-draw process, the counterpart of the deterministic fixed-`t` step. -/
theorem probEvent_saltSeq_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    Pr[(· = true) | saltSeq (Salt := Salt) c qSign] ≤ collisionBound Salt qSign qHash := by
  refine (probEvent_saltSeq_le Salt c qSign).trans ?_
  refine le_trans (Finset.sum_le_sum ?_) (sum_range_div_card_le_collisionBound Salt qSign qHash)
  intro j _
  gcongr
  exact_mod_cast hcache j

open Classical in
/-- **Salt-split tsum identity.** Weighting the uniform-draw distribution by `1` on a finite cache
`s` and by a constant `q` off it sums to `p + (1 - p) · q`, where `p = card s / |Salt|` is the
probability of landing in `s`. This is the inclusion-exclusion kernel underlying both the
salt-collision recursion `probEvent_saltSeq_succ` and the per-step charge of the salt-inclusive
coupling induction `signRunF_tvDist_le_saltSeq`. -/
theorem tsum_probOutput_uniformSample_ite (s : Finset Salt) (q : ℝ≥0∞) :
    (∑' x : Salt, Pr[= x | ($ᵗ Salt : ProbComp Salt)] * (if x ∈ s then 1 else q))
      = ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        + (1 - ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))) * q := by
  classical
  set p : ℝ≥0∞ := ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞)) with hp
  have hp_le : p ≤ 1 := by
    rw [hp, ← probEvent_mem_uniformSample (Salt := Salt) s]
    exact probEvent_le_one
  have hmem : Pr[(· ∈ s) | ($ᵗ Salt : ProbComp Salt)] = p := by
    rw [hp]; exact probEvent_mem_uniformSample (Salt := Salt) s
  have hcompl : Pr[(· ∉ s) | ($ᵗ Salt : ProbComp Salt)] = 1 - p := by
    have hsum := probEvent_compl (mx := ($ᵗ Salt : ProbComp Salt)) (· ∈ s)
    rw [hmem] at hsum
    have hbot : Pr[⊥ | ($ᵗ Salt : ProbComp Salt)] = 0 := by simp
    rw [hbot, tsub_zero] at hsum
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top hp_le) (by
      rw [add_comm]; exact hsum)
  have hsplit : ∀ x : Salt,
      Pr[= x | ($ᵗ Salt : ProbComp Salt)] * (if x ∈ s then 1 else q)
        = (if x ∈ s then Pr[= x | ($ᵗ Salt : ProbComp Salt)] else 0)
          + (if x ∈ s then 0 else Pr[= x | ($ᵗ Salt : ProbComp Salt)] * q) := by
    intro x; by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [hsplit]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [← probEvent_eq_tsum_ite]; exact hmem
  · have hre : ∀ x : Salt,
        (if x ∈ s then 0 else Pr[= x | ($ᵗ Salt : ProbComp Salt)] * q)
          = (if x ∉ s then Pr[= x | ($ᵗ Salt : ProbComp Salt)] else 0) * q := by
      intro x; by_cases hx : x ∈ s <;> simp [hx]
    simp_rw [hre]
    rw [ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite (p := (· ∉ s)), hcompl]

open Classical in
/-- **Exact one-step recursion of the salt-collision probability.** The probability that the
combined draw-then-check process `saltSeq c (n + 1)` reports a collision decomposes by independence
of the fresh head draw `r ← $ᵗ Salt` from the remaining `n` draws: with `p = card (c n) / |Salt|`
the head-collision probability, the head fires with probability `p`, and otherwise (probability
`1 - p`) the tail `saltSeq c n` must fire. Hence
`Pr[saltSeq c (n + 1)] = p + (1 - p) · Pr[saltSeq c n]`.

This is the tight inclusion-exclusion identity (the head draw and the tail are independent), the
per-step charge produced by the salt-inclusive coupling induction `signRunF_tvDist_le_saltSeq`. -/
theorem probEvent_saltSeq_succ (c : ℕ → Finset Salt) (n : ℕ) :
    Pr[(· = true) | saltSeq (Salt := Salt) c (n + 1)]
      = ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞)
        + (1 - ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
          * Pr[(· = true) | saltSeq (Salt := Salt) c n] := by
  classical
  set q : ℝ≥0∞ := Pr[(· = true) | saltSeq (Salt := Salt) c n] with hq
  -- Expand the head draw.
  conv_lhs => rw [saltSeq]
  rw [probEvent_bind_eq_tsum]
  -- Per-`r` inner probability: `1` if `r ∈ c n`, else `q`.
  have hinner : ∀ r : Salt,
      Pr[(· = true) | (saltSeq (Salt := Salt) c n >>=
            fun rest => (pure (decide (r ∈ c n) || rest) : ProbComp Bool))]
        = (if r ∈ c n then 1 else q) := by
    intro r
    by_cases hr : r ∈ c n
    · simp only [hr, if_true, decide_true, Bool.true_or]
      simp
    · simp only [hr, if_false, decide_false, Bool.false_or]
      rw [hq]
      simp
  simp_rw [hinner]
  exact tsum_probOutput_uniformSample_ite (Salt := Salt) (c n) q

/-! ## The salt-collision coupling and the hash-only granularity

The salt-averaged telescope above (`probEvent_saltSeq_le_collisionBound`) is the axiom-clean bound
on the GPV salt-collision event: a sequence of `qSign` fresh uniform salt draws, the `j`-th checked
against the recorded inputs `c j` of size `≤ j + qHash`, collides with probability at most
`collisionBound Salt qSign qHash`. This is the salt-AVERAGED combined "draw salt, then check" step
that a per-query `withProgramming` framework cannot express.

The `withProgramming` fire-on-miss bad event bounded by the U2 core
`tvDist_runtime_real_programmed_le_bad` cannot be supplied from this telescope at that statement's
granularity, for two independent structural reasons:

1. **Wrong event.** That bad event is the `withProgramming` *bad flag*, which fires on a
   cache-*miss* whose query input lies in the programming policy's support
   (`cache t = none ∧ policy t = some v`; see `QueryImpl.withProgramming`). For the GPV simulator
   policy (which programs at every fresh signing point) this fires *deterministically* once an
   uncached signing point is reached, so its probability is near `1`, not `collisionBound`. The
   salt-collision event of the telescope is the opposite: a fresh salt *hitting* an
   already-recorded entry (a cache *hit* at a programmed point), which the monotone fire-on-miss
   flag does not record.

2. **Invisible salt draws.** That bad event is phrased over `ob : OracleComp (Salt × M →ₒ Range)`, a
   random-oracle-only computation. The GPV signing salts are drawn in `unifSpec`/`ProbComp`, i.e.
   *outside* the `(Salt × M →ₒ Range)` spec, one step before each random-oracle query. By the time a
   query input `(r, m)` reaches the `withProgramming` handler the salt `r` is already a fixed value,
   so the `card / |Salt|` averaging that the telescope performs over the fresh draw is structurally
   absent from `ob`'s granularity.

The U2 *re-statement* `tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` (below)
states U2 over the salt-inclusive signing run with the bad event instrumented as the cache-HIT salt
collision `saltSeq c qSign`, and discharges the loss-free `tvDist ≤ collisionBound.toReal`
conclusion *given* the up-to-bad coupling
`hcouple : tvDist(real, programmed) ≤ Pr[saltSeq c qSign = true]`. It does **not** route through the
fire-on-miss bad event (which, per reason 1 above, would require the false inequality
"fire-on-miss ≤ salt-collision").  The GPV-instantiated Step-1 hop actually consumed by the headline
bounds is `gpv_tvDist_real_programmed_le_collisionBound`, which is unconditional over the pinned
game runs; the salt-inclusive re-statement is its hash-only surface analogue.

The coupling `hcouple` is the identical-until-bad coupling between the real GPV run (lazy random
oracle, fresh uniform answer at each `(r, m)`) and the programmed run (answer `psf.eval pk s`),
whose only divergence is a fresh signing salt colliding with a recorded cache slice — precisely the
`saltSeq` event. It is a joint distribution over the interleaved `unifSpec` salt-draw /
`(Salt × M →ₒ Range)` random-oracle-query streams of the salt-inclusive signing program, and is
established below over the salt-inclusive vehicle `signRunF` — where the salt draws are explicit —
rather than at the hash-only `ob` interface where they are invisible (reason 2). -/

/-! ## Salt-inclusive identical-until-bad coupling primitives

The coupling is built on a *salt-inclusive* signing process `signRunF`, where the salt draws are
explicit and the salt-collision averaging is structurally visible. This section establishes the
identical-until-bad primitives for that process.

`tvDist_signStep_real_programmed_le_collision` is the per-step core: a single combined "draw a fresh
salt `r`, then answer" step, where the *real* branch answers with the lazy random-oracle value and
the *programmed* branch answers with the regularity-supplied value. Off the per-step salt collision
`r ∈ cache`, regularity makes the two answer branches agree in distribution (`h_eq`), so the
total-variation distance of the combined step is bounded by exactly the salt collision probability
`card cache / |Salt|`. This is the single-step instance of the fundamental-lemma-of-game-playing,
with the bad event averaged over the fresh salt draw. It specializes
`tvDist_bind_left_event_le`.

`signRunF` is the flag-carrying sequenced signing process: it draws `qSign` fresh salts in turn,
applies a per-step answer handler `step n state r`, and sets a Boolean flag the first time a drawn
salt lands in its recorded cache slice `c n`. Its flag-true marginal is the run-level counterpart of
the `saltSeq` collision event: the flag fires iff some draw collides, which is exactly the
`saltSeq` disjunction marginalized over the threaded state.

`signRunF_tvDist_le_saltSeq` is the multi-step coupling: the total-variation distance between the
real and programmed sequenced runs is bounded by `Pr[saltSeq c qSign = true]`. Off the per-step
collision the *current* step distributions agree (via `h_step`), but the two runs recurse with
*different* per-step handlers, so the off-bad agreement is threaded through the recursion with the
accumulating flag rather than obtained by a single application of the per-step primitive (the tails
differ). Chaining it with the telescope `probEvent_saltSeq_le_collisionBound` yields the
salt-inclusive coupling `signRunF_tvDist_le_collisionBound`. -/

omit [DecidableEq Salt] [Fintype Salt] in
/-- **Per-step salt-inclusive identical-until-bad coupling.**

A single combined "draw a fresh salt `r`, then answer" step. The *real* answer branch `freal r` and
the *programmed* answer branch `fprog r` are coupled through the shared fresh salt draw. Off the
per-step salt collision `r ∈ cache`, regularity guarantees the two answer branches agree in
distribution (`h_eq`), so the total-variation distance of the combined step is bounded by the
probability that the fresh salt lands in `cache`, namely `card cache / |Salt|` (via
`probEvent_mem_uniformSample`).

This is the single-step instance of the fundamental-lemma-of-game-playing with the bad event
averaged over the fresh salt draw. It specializes `tvDist_bind_left_event_le` at
`mx := $ᵗ Salt` and `bad := (· ∈ cache)`. It is the per-step core the sequenced coupling
`signRunF_tvDist_le_saltSeq` accumulates. -/
theorem tvDist_signStep_real_programmed_le_collision [Nonempty Salt] {β : Type}
    (cache : Finset Salt) (freal fprog : Salt → ProbComp β)
    (h_eq : ∀ r, r ∉ cache → 𝒮[freal r] = 𝒮[fprog r]) :
    tvDist
        (do let r ← ($ᵗ Salt : ProbComp Salt); freal r)
        (do let r ← ($ᵗ Salt : ProbComp Salt); fprog r)
      ≤ (Pr[(· ∈ cache) | ($ᵗ Salt : ProbComp Salt)]).toReal :=
  tvDist_bind_left_event_le _ freal fprog (· ∈ cache) h_eq

open Classical in
/-- **Flag-carrying sequenced signing process.**

`signRunF step c n` runs `n` combined signing steps over a threaded state `St × Bool`. At step `j`
it draws a fresh salt `r ← $ᵗ Salt`, advances the state by the per-step handler `step j state r`,
and records in the Boolean flag whether `r` landed in the recorded cache slice `c j`. The flag is
monotone (set once a collision occurs), so its final value is the run-level salt-collision event —
the salt-inclusive, state-threaded counterpart of the salt-averaged `saltSeq` process. -/
noncomputable def signRunF {St : Type} (step : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) : (n : ℕ) → St × Bool → ProbComp (St × Bool)
  | 0, sb => pure sb
  | (n + 1), sb => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let st' ← step n sb.1 r
      signRunF step c n (st', sb.2 || decide (r ∈ c n))

omit [Fintype Salt] in
/-- **`signRunF` never fails when its step never fails.** If every per-step handler `step n s r`
never fails, the whole `qSign`-step `signRunF` recursion never fails: the leading uniform salt draw
is total, the step is total by hypothesis, and the tail never fails by induction. Consequently its
output distribution has total mass one, so it can be discarded as a value-irrelevant never-failing
prefix (`evalSPMF_bind_const_neverFails`) — the tape-suffix-discard step of a fold factorization. -/
theorem signRunF_neverFail {St : Type} [Nonempty Salt]
    (step : ℕ → St → Salt → ProbComp St) (c : ℕ → Finset Salt)
    [hstep : ∀ n s r, NeverFail (step n s r)] :
    ∀ (n : ℕ) (sb : St × Bool), NeverFail (signRunF (Salt := Salt) step c n sb) := by
  intro n
  induction n with
  | zero => intro sb; exact inferInstanceAs (NeverFail (pure sb))
  | succ n ih =>
      intro sb
      refine (neverFail_bind_iff _ _).2 ⟨inferInstance, fun r _ => ?_⟩
      exact (neverFail_bind_iff _ _).2 ⟨hstep n sb.1 r, fun st' _ => ih _⟩

omit [Fintype Salt] in
/-- **Discarding the `signRunF` salt prefix.** When the per-step handler never fails, the entire
`signRunF` recursion never fails (`signRunF_neverFail`), so binding a *value-irrelevant*
continuation `k` after it contributes only `signRunF`'s total mass one: the salt-draw prefix is
discarded from the output distribution. This is the GPV `signRunF` instance of the generic
never-failing-prefix discard `evalSPMF_bind_const_neverFails`; it is the move that drops the
over-provisioned front salt tape once the genuine content has been spliced out, the analogue of the
`drawList` suffix discard in the worked Fiat–Shamir factorization. -/
theorem evalSPMF_signRunF_bind_const {St γ : Type} [Nonempty Salt]
    (step : ℕ → St → Salt → ProbComp St) (c : ℕ → Finset Salt)
    [∀ n s r, NeverFail (step n s r)] (n : ℕ) (sb : St × Bool) (k : ProbComp γ) :
    𝒮[signRunF (Salt := Salt) step c n sb >>= fun _ => k] = 𝒮[k] := by
  have := signRunF_neverFail (Salt := Salt) step c n sb
  refine SPMF.ext fun x => ?_
  set sr := signRunF (Salt := Salt) step c n sb with hsr
  rw [show 𝒮[sr >>= fun _ => k] x = Pr[= x | sr >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒮[k] x = Pr[= x | k] from (probOutput_def _ _).symm,
    probOutput_bind_const, probFailure_eq_zero]
  simp

omit [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] in
/-- **Uniform per-fibre TV bound for a shared base.** If two continuations are pointwise at
total-variation distance at most `δ` (with `δ ≥ 0`), then binding them over a common base
computation is also within `δ`. The base only needs to be a sub-probability computation; the mass
`∑' Pr[= a] ≤ 1` absorbs the constant fibre bound. -/
theorem tvDist_bind_le_of_forall_le {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β)
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ a, tvDist (f a) (g a) ≤ δ) :
    tvDist (mx >>= f) (mx >>= g) ≤ δ := by
  refine le_trans (tvDist_bind_left_le mx f g) ?_
  have hbase : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  have hsum_le_one : ∑' a : α, Pr[= a | mx].toReal ≤ 1 := by
    have h1 : (∑' a : α, Pr[= a | mx].toReal) = (∑' a : α, Pr[= a | mx]).toReal :=
      (ENNReal.tsum_toReal_eq (fun a => ne_top_of_le_ne_top one_ne_top probOutput_le_one)).symm
    rw [h1, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      one_ne_top).2 tsum_probOutput_le_one
  calc ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a)
        ≤ ∑' a, Pr[= a | mx].toReal * δ :=
        Summable.tsum_le_tsum
          (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
          (Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg) (hbase.mul_right δ))
          (hbase.mul_right δ)
    _ = (∑' a, Pr[= a | mx].toReal) * δ := by rw [tsum_mul_right]
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hsum_le_one hδ
    _ = δ := one_mul δ

open Classical in
omit [Fintype Salt] in
/-- **Stateful identical-until-bad telescoping (generalized over the initial flag and state).**

This is the inductive heart of the salt-inclusive coupling. For any initial flag `b` and state
`st`, the total-variation distance between the real and programmed sequenced runs is bounded by the
salt-averaged collision probability `Pr[saltSeq c n = true]`, *independently of `b` and `st`* (the
flag only accumulates the collision disjunction and the RHS does not depend on the threaded state).

The successor step shares the fresh salt draw `r ← $ᵗ Salt` and splits per-`r`:
* On the per-step collision `r ∈ c n` the step is charged its full mass (`tvDist ≤ 1`), contributing
  the head term `card (c n) / |Salt|`.
* Off the collision (`r ∉ c n`) the head handlers agree in distribution (`h_step`), so by the
  triangle inequality the step contributes only the tail, bounded by the induction hypothesis at the
  advanced state and flag. The `NeverFail` hypothesis keeps the state-marginal mass equal to one.

The per-`r` charges accumulate to exactly `card (c n) / |Salt| + (1 - card (c n) / |Salt|) ·
Pr[saltSeq c n]`, which equals `Pr[saltSeq c (n + 1)]` by the independence identity
`probEvent_saltSeq_succ`. This realizes design L3a: a stateful telescoping accepting
state-dependent per-step costs. -/
theorem signRunF_tvDist_le_saltSeq_aux {St : Type} [Finite Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒮[stepReal n st r] = 𝒮[stepProg n st r])
    (n : ℕ) (st : St) (b : Bool) :
    tvDist (signRunF (Salt := Salt) stepReal c n (st, b))
        (signRunF (Salt := Salt) stepProg c n (st, b))
      ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c n]).toReal := by
  classical
  have : Fintype Salt := Fintype.ofFinite Salt
  induction n generalizing st b with
  | zero =>
      simp only [signRunF]
      rw [tvDist_self]
      exact ENNReal.toReal_nonneg
  | succ n ih =>
      -- Notation for the per-step head-collision probability `p` and tail probability `q`.
      set q : ℝ≥0∞ := Pr[(· = true) | saltSeq (Salt := Salt) c n] with hq
      set p : ℝ≥0∞ := ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) with hp
      have hp_le : p ≤ 1 := by
        rw [hp, ← probEvent_mem_uniformSample (Salt := Salt) (c n)]
        exact probEvent_le_one
      have hq_le : q ≤ 1 := by rw [hq]; exact probEvent_le_one
      -- Unfold one step on both sides; the salt draw `r ← $ᵗ Salt` is shared.
      rw [signRunF, signRunF]
      -- Per-`r` continuation bound.
      refine le_trans (tvDist_bind_left_le ($ᵗ Salt : ProbComp Salt) _ _) ?_
      -- Bound each per-`r` term by `if r ∈ c n then 1 else q.toReal`.
      have hterm : ∀ r : Salt,
          tvDist (stepReal n st r >>= fun st' =>
              signRunF (Salt := Salt) stepReal c n (st', b || decide (r ∈ c n)))
            (stepProg n st r >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
            ≤ (if r ∈ c n then 1 else q.toReal) := by
        intro r
        by_cases hr : r ∈ c n
        · rw [if_pos hr]; exact tvDist_le_one _ _
        · rw [if_neg hr]
          -- Triangle through the real head with the programmed tail.
          refine le_trans (tvDist_triangle _
            (stepReal n st r >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n))) _) ?_
          have htail : tvDist (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepReal c n (st', b || decide (r ∈ c n)))
              (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              ≤ q.toReal :=
            tvDist_bind_le_of_forall_le (stepReal n st r) _ _ q.toReal ENNReal.toReal_nonneg
              (fun st' => ih st' (b || decide (r ∈ c n)))
          have hhead : tvDist (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              (stepProg n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              = 0 := by
            rw [tvDist_eq_zero_iff, evalSPMF_bind, evalSPMF_bind, h_step n st r hr]
          rw [hhead, add_zero]
          exact htail
      -- Normalize the product projections `(st, b).1`, `(st, b).2` to `st`, `b`.
      change (∑' a : Salt, Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal *
          tvDist (stepReal n st a >>= fun st' =>
              signRunF (Salt := Salt) stepReal c n (st', b || decide (a ∈ c n)))
            (stepProg n st a >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (a ∈ c n))))
        ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c (n + 1)]).toReal
      -- `q.toReal ≤ 1` and base summability.
      have hq_toReal_le : q.toReal ≤ 1 := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal probEvent_ne_top one_ne_top).2 hq_le
      have hbase : Summable (fun a : Salt => Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal) :=
        ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      have hcap : ∀ a : Salt, (if a ∈ c n then (1 : ℝ) else q.toReal) ≤ 1 := by
        intro a; split_ifs with ha
        · exact le_refl 1
        · exact hq_toReal_le
      have hcap_nonneg : ∀ a : Salt, (0 : ℝ) ≤ (if a ∈ c n then (1 : ℝ) else q.toReal) := by
        intro a; split_ifs <;> [norm_num; exact ENNReal.toReal_nonneg]
      -- Summability of the salt-split bounding sum.
      have hsummable_term : Summable (fun a : Salt =>
          Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal * (if a ∈ c n then 1 else q.toReal)) :=
        Summable.of_nonneg_of_le
          (fun a => mul_nonneg ENNReal.toReal_nonneg (hcap_nonneg a))
          (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (hcap a)) hbase
      -- Summability of the actual tvDist-weighted sum.
      have hsummable_tv : Summable (fun a : Salt =>
          Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal *
            tvDist (stepReal n st a >>= fun st' =>
                signRunF (Salt := Salt) stepReal c n (st', b || decide (a ∈ c n)))
              (stepProg n st a >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (a ∈ c n)))) :=
        Summable.of_nonneg_of_le
          (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
          (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg
            ((hterm a).trans (hcap a))) hbase
      refine le_trans (Summable.tsum_le_tsum (fun a =>
        mul_le_mul_of_nonneg_left (hterm a) ENNReal.toReal_nonneg)
        hsummable_tv hsummable_term) ?_
      -- Identify the salt-split sum with `Pr[saltSeq c (n+1)].toReal`.
      -- Each real term is the `toReal` of the corresponding `ℝ≥0∞` term.
      have hterm_toReal : ∀ i : Salt,
          Pr[= i | ($ᵗ Salt : ProbComp Salt)].toReal * (if i ∈ c n then (1 : ℝ) else q.toReal)
            = (Pr[= i | ($ᵗ Salt : ProbComp Salt)] * (if i ∈ c n then 1 else q)).toReal := by
        intro i
        by_cases hi : i ∈ c n <;> simp [hi]
      simp_rw [hterm_toReal]
      -- Pull the `toReal` out of the sum (each term is finite), evaluate, and identify.
      rw [← ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top
        (ne_top_of_le_ne_top one_ne_top probOutput_le_one) (by
          split_ifs <;> [exact one_ne_top; exact probEvent_ne_top])),
        tsum_probOutput_uniformSample_ite (Salt := Salt) (c n) q, ← probEvent_saltSeq_succ]

omit [Fintype Salt] in
/-- **Salt-inclusive identical-until-bad coupling.**

The total-variation distance between the real sequenced signing run `signRunF stepReal c n` and the
programmed sequenced signing run `signRunF stepProg c n` is bounded by the salt-averaged collision
probability `Pr[saltSeq c n = true]`, provided the two per-step handlers agree in distribution off
the per-step salt collision `r ∈ c j` (`h_step`, supplied for GPV by regularity `hreg`). The
`NeverFail` hypothesis on the real handler keeps probability mass during the state marginalization.

This is the multi-step joint coupling, threaded through the recursion by
`signRunF_tvDist_le_saltSeq_aux` (the generalization over the initial flag and state). It decomposes
into two parts:

* **Per-step charge.** Off `r ∈ c j` the two combined "draw salt, then answer" steps agree in
  distribution, so each step contributes only its salt-collision mass `card (c j) / |Salt|`. This is
  the per-step primitive `tvDist_signStep_real_programmed_le_collision`, applied per fibre
  via `tvDist_bind_le_of_forall_le`.
* **Accumulation to `saltSeq`.** The per-step charges accumulate along the recursion to the
  run-level collision-flag probability, which equals the salt-averaged `saltSeq` disjunction once
  the threaded state is marginalized out — the inclusion-exclusion identity
  `probEvent_saltSeq_succ`.

Chaining this result with the telescope `probEvent_saltSeq_le_collisionBound`
(`Pr[saltSeq] ≤ collisionBound`) yields the salt-inclusive coupling that discharges the U2
hypothesis `hcouple`, once the GPV reduction handlers and per-step caches `c j` are instantiated. -/
theorem signRunF_tvDist_le_saltSeq {St : Type} [Finite Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒮[stepReal n st r] = 𝒮[stepProg n st r])
    (n : ℕ) (st : St) :
    tvDist (signRunF (Salt := Salt) stepReal c n (st, false))
        (signRunF (Salt := Salt) stepProg c n (st, false))
      ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c n]).toReal :=
  signRunF_tvDist_le_saltSeq_aux (Salt := Salt) (St := St)
    stepReal stepProg c h_step n st false

/-- **U2, re-stated over the salt-inclusive signing run (unconditional).**

This is the salt-inclusive U2: it bounds the total-variation distance between the real and
programmed *signing runs* directly by `collisionBound`, with **no coupling hypothesis**. Unlike the
hash-only `tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` (which takes the coupling
as the typed hypothesis `hcouple`), this lemma is phrased over the salt-inclusive vehicle
`signRunF` — where each of the `qSign` fresh signing salts `r ← $ᵗ Salt` is an explicit step of the
recursion — so the salt-collision averaging is *structurally visible* and the coupling discharges it
outright.

The proof chains two results with no loss:
* the multi-step coupling `signRunF_tvDist_le_saltSeq`
  (`tvDist (signRunF stepReal …) (signRunF stepProg …) ≤ Pr[saltSeq c qSign = true]`), and
* the salt-averaged telescope `probEvent_saltSeq_le_collisionBound`
  (`Pr[saltSeq c qSign = true] ≤ collisionBound Salt qSign qHash`),
moved to `ℝ` by `ENNReal.toReal_mono` (using `collisionBound < ⊤`).

`stepReal`/`stepProg` are the per-signing-step answer handlers (real lazy random oracle vs the
regularity-supplied programmed answer); `h_step` is the off-collision branch agreement supplied by
PSF regularity (`psf.Regularity`); `c j` is the recorded random-oracle cache slice seen by the
`j`-th signing query, with the standard growth bound `card (c j) ≤ j + qHash` (`hcache`).

Feeding the four GPV theorems additionally requires the adaptive→`signRunF` factorization: matching
the real adversary run `simulateQ impl (adv.main pk)` — which interleaves the `qSign` signing
queries (each drawing a fresh salt) with up to `qHash` adversary hash queries *adaptively* — to this
fixed `qSign`-step `signRunF` recursion. That factorization is the deferred-sampling joint coupling
packaged as `AdaptiveFactorizesSignRunF` (see the *Adaptive→signRunF factorization* section
below). -/
theorem signRunF_tvDist_le_collisionBound {St : Type} [Finite Salt] [Nonempty Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒮[stepReal n st r] = 𝒮[stepProg n st r])
    (qSign qHash : ℕ) (hcache : ∀ j, (c j).card ≤ j + qHash) (st : St) :
    tvDist (signRunF (Salt := Salt) stepReal c qSign (st, false))
        (signRunF (Salt := Salt) stepProg c qSign (st, false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  refine (signRunF_tvDist_le_saltSeq (Salt := Salt) stepReal stepProg c h_step qSign st).trans ?_
  refine ENNReal.toReal_mono ?_ (probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache)
  refine (ENNReal.div_lt_top ?_ ?_).ne
  · simp
  · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
    exact Fintype.card_ne_zero

end GPVHashAndSign
