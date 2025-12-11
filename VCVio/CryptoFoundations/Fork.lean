/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Append

/-!
# Forking Lemma

-/

open OracleSpec OracleComp Option ENNReal Function

section scratch

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ δ : Type v}

lemma probOutput_prod_mk_seq_map_eq_mul [spec.FiniteRange] (oa : OracleComp spec α)
    (ob : OracleComp spec β) (z : α × β) :
    [= z | ((·, ·) <$> oa <*> ob : OracleComp spec (α × β))] = [= z.1 | oa] * [= z.2 | ob] := by
    obtain ⟨fst, snd⟩ := z
    simp_all only [probOutput_seq_map_prod_mk_eq_mul]

lemma probOutput_prod_mk_seq_map_eq_mul' [spec.FiniteRange] (oa : OracleComp spec α)
    (ob : OracleComp spec β) (x : α) (y : β) :
    [= (x, y) | ((·, ·) <$> oa <*> ob : OracleComp spec (α × β))] = [= x | oa] * [= y | ob] := by
    simp_all only [probOutput_seq_map_prod_mk_eq_mul]

lemma probOutput_prod_mk_apply_seq_map_eq_mul [spec.FiniteRange] (oa : OracleComp spec α)
    (ob : OracleComp spec β)
    (f : α → γ) (g : β → δ) (z : γ × δ) :
    [= z | (f ·, g ·) <$> oa <*> ob] = [= z.1 | f <$> oa] * [= z.2 | g <$> ob] := by
  sorry

lemma probOutput_prod_mk_apply_seq_map_eq_mul' [spec.FiniteRange] (oa : OracleComp spec α)
    (ob : OracleComp spec β)
    (f : α → γ) (g : β → δ) (x : γ) (y : δ) :
    [= (x, y) | (f ·, g ·) <$> oa <*> ob] = [= x | f <$> oa] * [= y | g <$> ob] := by
    rw [@probOutput_prod_mk_apply_seq_map_eq_mul]

lemma probOutput_bind_bind_prod_mk_eq_mul [spec.FiniteRange] (oa : OracleComp spec α)
    (ob : OracleComp spec β) (f : α → γ) (g : β → δ) (z : γ × δ) :
    [= z | do let x ← oa; let y ← ob; return (f x, g y)] =
      [= z.1 | f <$> oa] * [= z.2 | g <$> ob] := by
  sorry

@[simp]
lemma probOutput_bind_bind_prod_mk_eq_mul' [spec.FiniteRange] (oa : OracleComp spec α)
    (ob : OracleComp spec β) (f : α → γ) (g : β → δ) (x : γ) (y : δ) :
    [= (x, y) | do let x ← oa; let y ← ob; return (f x, g y)] =
      [= x | f <$> oa] * [= y | g <$> ob] := by
      rw [@probOutput_bind_bind_prod_mk_eq_mul]

lemma map_ite (oa₁ oa₂ : OracleComp spec α) (f : α → β) (p : Prop) [Decidable p] :
    f <$> (if p then oa₁ else oa₂) = if p then (f <$> oa₁) else (f <$> oa₂) := by
    rw [← @apply_ite]

lemma probFailure_bind_eq_sum_probFailure [spec.FiniteRange] (oa : OracleComp spec α)
    {ob : α → OracleComp spec β} {σ : Type u} {s : Finset σ}
    {oc : σ → α → OracleComp spec γ} :
    [⊥ | oa >>= ob] = ∑ x ∈ s, [⊥ | oa >>= oc x] := by
  sorry

lemma probOutput_map_eq_probEvent [spec.FiniteRange]
    (oa : OracleComp spec α) (f : α → β) (y : β) :
    [= y | f <$> oa] = [fun x => f x = y | oa] := by
  rw [← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def]

@[simp]
lemma probOutput_prod_mk_fst_map [spec.FiniteRange] (oa : OracleComp spec α) (y : β) (z : α × β) :
    [= z | (·, y) <$> oa] = [= z.1 | oa] * [= z.2 | (pure y : OracleComp spec β)] := by
  sorry

@[simp]
lemma probOutput_prod_mk_snd_map [spec.FiniteRange] (ob : OracleComp spec β) (x : α) (z : α × β) :
    [= z | (x, ·) <$> ob] = [= z.1 | (pure x : OracleComp spec α)] * [= z.2 | ob] := by
  sorry

@[simp]
lemma probOutput_prod_mk_fst_map' [spec.FiniteRange] (oa : OracleComp spec α)
    (f : α → γ) (y : β) (z : γ × β) :
    [= z | (f ·, y) <$> oa] = [= z.1 | f <$> oa] * [= z.2 | (pure y : OracleComp spec β)] := by
  sorry

@[simp]
lemma probOutput_prod_mk_snd_map' [spec.FiniteRange] (ob : OracleComp spec β)
    (f : β → γ) (x : α) (z : α × γ) :
    [= z | (x, f ·) <$> ob] = [= z.1 | (pure x : OracleComp spec α)] * [= z.2 | f <$> ob] := by
  sorry

lemma probOutput_bind_ite_failure_eq_tsum [spec.FiniteRange] [DecidableEq β]
    (oa : OracleComp spec α) (f : α → β) (p : α → Prop) [DecidablePred p] (y : β) :
    [= y | oa >>= fun x => if p x then pure (f x) else failure] =
      ∑' x : α, if p x ∧ y = f x then [= x | oa] else 0 := by
  rw [probOutput_bind_eq_tsum]
  simp [probEvent_eq_tsum_ite, ite_and]

-- lemma probOutput_eq

end scratch

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SelectableType (spec.range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α β γ : Type}

structure forkInput (spec : OracleSpec ι) (α : Type) where
  /-- The main program to fork execution of -/
  main : OracleComp spec α
  /-- A bound on the number of queries the adversary makes-/
  queryBound : ι → ℕ
  /-- List of oracles that are queried during computation (used to order seed generation). -/
  js : List ι

/-- Version of `fork` that doesn't choose `s` ahead of time.
Should give better concrete bounds. -/
def fork (main : OracleComp spec α)
    (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (α × α) := do
  let seed ← generateSeed spec qb js
  let x₁ ← (simulateQ seededOracle main).run seed
  let s : Fin (qb i + 1) ← (cf x₁).getM
  let u ←$ᵗ spec.range i -- Choose new output for query
  guard ((seed i)[s + 1]? ≠ some u) -- Didn't pick the same output
  let seed' := (seed.takeAtIndex i s).addValue i u
  let x₂ ← (simulateQ seededOracle main).run seed'
  guard (cf x₂ = some s) -- Choose the same index on this run
  return (x₁, x₂)

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1))) [spec.FiniteRange]

@[simp] lemma support_map_prod_map_fork : (Prod.map cf cf <$> main.fork qb js i cf).support =
    (fun s => (s, s)) '' (cf <$> main).support := by
  sorry

@[simp] lemma finSupport_map_prod_map_fork : (Prod.map cf cf <$> main.fork qb js i cf).finSupport =
    (cf <$> main).finSupport.image fun s => (s, s) := by
  sorry

lemma apply_eq_apply_of_mem_support_fork (x₁ x₂ : α)
    (h : (x₁, x₂) ∈ (fork main qb js i cf).support) : cf x₁ = cf x₂ := by
  sorry

@[simp] lemma probOutput_none_map_fork_left (s : Option (Fin (qb i + 1))) :
    [= (none, s) | Prod.map cf cf <$> main.fork qb js i cf] = 0 := by
  sorry

@[simp] lemma probOutput_none_map_fork_right (s : Option (Fin (qb i + 1))) :
    [= (s, none) | Prod.map cf cf <$> main.fork qb js i cf] = 0 := by
  sorry

theorem exists_log_of_mem_support_fork (x₁ x₂ : α)
    (h : (x₁, x₂) ∈ (fork main qb js i cf).support) :
      ∃ s, cf x₁ = some s ∧ cf x₂ = some s ∧
      ∃ log₁ : QueryLog spec, ∃ hcf₁ : ↑s < log₁.countQ i,
      ∃ log₂ : QueryLog spec, ∃ hcf₁ : ↑s < log₂.countQ i,
      (log₁.getQ i)[s].1 = (log₂.getQ i)[s].1 ∧
      (log₁.getQ i)[s].2 ≠ (log₂.getQ i)[s].2 ∧
      (x₁, log₁) ∈ (simulateQ loggingOracle main).run.support ∧
      (x₂, log₂) ∈ (simulateQ loggingOracle main).run.support := by
  sorry

lemma le_probOutput_fork (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
    [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h
      ≤ [= (s, s) | Prod.map cf cf <$> fork main qb js i cf] :=
  let h : ℝ≥0∞ := ↑(Fintype.card (spec.range i))
  have : DecidableEq α := Classical.decEq α -- :(
  have : DecidableEq spec.QuerySeed := Classical.decEq _
  calc [= (s, s) | Prod.map cf cf <$> fork main qb js i cf]
    _ = [fun (x₁, x₂) => cf x₁ = s ∧ cf x₂ = s | fork main qb js i cf] := by {
      simp [probOutput_map_eq_tsum_ite, probEvent_eq_tsum_ite,
        Prod.eq_iff_fst_eq_snd_eq, @eq_comm _ (some s)]
    }
    _ = [= (s, s) | Prod.map cf cf <$> fork main qb js i cf] := by {
        simp [probOutput_map_eq_probEvent, Prod.eq_iff_fst_eq_snd_eq]
      }
    _ = [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? ≠ u)
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] := by {
        simp [fork]
        refine probOutput_bind_congr fun _ _ => ?_
        refine probOutput_bind_congr fun x₁ hx₁ => ?_
        by_cases hcfx₁ : cf x₁ = s
        · simp [hcfx₁]
          refine probOutput_bind_congr fun _ _ => ?_
          refine probOutput_bind_congr fun () _ => ?_
          simp [apply_ite]
          rw [probOutput_bind_ite_failure_eq_tsum, probOutput_map_eq_tsum]
          simp
          refine tsum_congr fun x₂ => ?_
          by_cases hcfx₂ : cf x₂ = s
          · simp [hcfx₂]
          · simp [hcfx₂, Ne.symm hcfx₂]
        · refine (?_ : _ = (0 : ℝ≥0∞)).trans (?_ : (0 : ℝ≥0∞) = _)
          · simp [hcfx₁]
          · simp [hcfx₁]
      }
    _ ≥ [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] -
        [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? = u)
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] := by {
        rw [ge_iff_le]
        refine probOutput_bind_congr_sub_le fun seed hseed => ?_
        refine probOutput_bind_congr_sub_le fun x₁ hx₁ => ?_
        by_cases hcfx₁ : cf x₁ = s
        · simp [hcfx₁]
          refine probOutput_bind_congr_le_add fun u hu => ?_
          by_cases hu' : (seed i)[(↑(s + 1) : ℕ)]? = some u
          · simp [hu']
          · simp [hu']
        · refine le_of_eq_of_le ?_ zero_le'
          refine tsub_eq_zero_of_le (le_of_eq_of_le ?_ zero_le')
          simp [hcfx₁]
      }
    _ ≥ [= (s, s) | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          let seed' := (seed.takeAtIndex i s).addValue i u
          let x₂ ← (simulateQ seededOracle main).run seed'
          return (cf x₁, cf x₂)] -
        [= s | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          let u ←$ᵗ spec.range i
          guard ((seed i)[s + 1]? = u)
          return (cf x₁)] := by {
        refine tsub_le_tsub le_rfl ?_
        refine probOutput_bind_mono fun seed hseed => ?_
        refine probOutput_bind_mono fun x₁ hx₁ => ?_
        refine probOutput_bind_mono fun u hu => ?_
        refine probOutput_bind_mono fun () _ => ?_
        by_cases hcfx₁ : some s = cf x₁
        · simp [hcfx₁]
        · simp [hcfx₁]
      }
    _ = [= (s, s) | do
          let shared_seed ← liftM (generateSeed spec (Function.update qb i s) js)
          let x₁ ← (simulateQ seededOracle main).run shared_seed
          let x₂ ← (simulateQ seededOracle main).run shared_seed
          return (cf x₁, cf x₂)] -
        [= s | do
          let seed ← liftM (generateSeed spec qb js)
          let x₁ ← (simulateQ seededOracle main).run seed
          return (cf x₁)] / h := by {
        congr 1
        · sorry
        · refine probOutput_bind_congr_div_const fun seed hseed => ?_
          have : (↑(s + 1) : ℕ) < (seed i).length := by sorry
          let u : spec.range i := ((seed i)[↑(s + 1)])
          simp [probOutput_bind_eq_tsum, probOutput_map_eq_tsum, div_eq_mul_inv,
            ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun x => ?_
          refine (tsum_eq_single ((seed i)[(↑(s + 1) : ℕ)]) ?_).trans ?_
          · intro u' hu'
            rw [List.getElem?_eq_getElem this]
            simp [hu'.symm]
          · simp [h]
      }
    _ = ∑ seed ∈ (generateSeed spec (Function.update qb i s) js).finSupport,
          ((generateSeed spec (Function.update qb i s) js).finSupport.card : ℝ≥0∞)⁻¹ * [= (s, s) | do
            let x₁ ← (simulateQ seededOracle main).run seed
            let x₂ ← (simulateQ seededOracle main).run seed
            return (cf x₁, cf x₂)] - [= s | cf <$> main] / h := by {
        congr 1
        · rw [probOutput_bind_eq_sum_finSupport]
          simp only [liftM_eq_liftComp, finSupport_liftComp, probOutput_liftComp, bind_pure_comp, h]
          refine Finset.sum_congr rfl fun seed hseed => ?_
          congr 1
          apply probOutput_generateSeed'
          refine mem_support_of_mem_finSupport _ hseed
        · rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
          refine (ENNReal.mul_right_inj (by simp [h]) (by simp [h])).2 ?_
          simp
      }
    _ = ((generateSeed spec (Function.update qb i s) js).finSupport.card : ℝ≥0∞)⁻¹ *
          ∑ seed ∈ (generateSeed spec (Function.update qb i s) js).finSupport,
            [= s | cf <$> (simulateQ seededOracle main).run seed] ^ 2 - [= s | cf <$> main] / h := by {
        rw [Finset.mul_sum]
        congr 2
        simp only [probOutput_bind_bind_prod_mk_eq_mul', pow_two]
      }
    _ ≥ ((generateSeed spec (Function.update qb i s) js).finSupport.card : ℝ≥0∞)⁻¹ ^ 2 *
          (∑ seed ∈ (generateSeed spec (Function.update qb i s) js).finSupport,
            [= s | cf <$> (simulateQ seededOracle main).run seed]) ^ 2 - [= s | cf <$> main] / h := by {
        refine tsub_le_tsub ?_ le_rfl
        have := ENNReal.rpow_sum_le_const_mul_sum_rpow
          ((generateSeed spec (Function.update qb i s) js).finSupport)
          (fun seed => [= s | cf <$> (simulateQ seededOracle main).run seed])
          (one_le_two)
        simp only [] at this
        have hc : ((finSupport (generateSeed spec (update qb i ↑s) js)).card : ℝ≥0∞)⁻¹ ^ 2 ≠ 0 := by {
          simp
        }
        have := ((ENNReal.mul_le_mul_left hc (by simp)).2 this)
        simp only [rpow_two] at this
        refine le_trans this ?_
        rw [← mul_assoc]
        refine le_of_eq ?_
        refine congr_arg (· * _) ?_
        norm_num
        rw [pow_two, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
        · simp
        · simp
      }
    _ = [= s | do
          let seed ← liftM (generateSeed spec ((Function.update qb i s)) js)
          cf <$> (simulateQ seededOracle main).run seed] ^ 2 - [= s | cf <$> main] / h := by {
        rw [probOutput_bind_eq_sum_finSupport]
        congr 1
        rw [← mul_pow, Finset.mul_sum]
        refine congr_arg (· ^ 2) ?_
        refine Finset.sum_congr (finSupport_liftComp _ _).symm fun seed hseed => ?_
        rw [liftM_eq_liftComp, probOutput_liftComp, probOutput_generateSeed']
        refine mem_support_of_mem_finSupport _ ?_
        simpa using hseed
      }
    _ = [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h := by {
        simp only [liftM_eq_liftComp, seededOracle.probOutput_generateSeed_bind_map_simulateQ, h]
      }

theorem probFailure_fork_le :
    let acc : ℝ≥0∞ := ∑ s, [= some s | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.range i)
    let q := qb i + 1
    [⊥ | fork main qb js i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  let acc : ℝ≥0∞ := ∑ s, [= some s | cf <$> main]
  let h : ℝ≥0∞ := Fintype.card (spec.range i)
  let q := qb i + 1
  calc [⊥ | fork main qb js i cf]
    _ = 1 - ∑ s, [= (some s, some s) | Prod.map cf cf <$> fork main qb js i cf] := by
      have := (probFailure_eq_sub_sum_probOutput_map (fork main qb js i cf) (Prod.map cf cf))
      rw [this]
      refine congr_arg (_ - ·) ?_ --
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_option]
      simp
      refine (Finset.sum_congr rfl fun s hs => ?_)
      refine Finset.sum_eq_single _ ?_ (by simp)
      simp
      tauto
    _ ≤ 1 - ∑ s, ([= some s | cf <$> main] ^ 2 - [= some s | cf <$> main] / h) := by
      refine tsub_le_tsub le_rfl ?_
      refine Finset.sum_le_sum fun s _ => ?_
      have := le_probOutput_fork main qb js i cf s
      exact this
    _ ≤ 1 - ((∑ s, [= some s | cf <$> main] ^ 2) - (∑ s, [= some s | cf <$> main] / h)) := by
      refine tsub_le_tsub le_rfl ?_
      sorry -- Hypothesis that `h` is sufficiently large
    _ = 1 - (∑ s, [= some s | cf <$> main] ^ 2) + (∑ s, [= some s | cf <$> main] / h) := by
      sorry -- Hypothesis that `h` is sufficiently large
    _ ≤ 1 - (∑ s, [= some s | cf <$> main]) ^ 2 / q + (∑ s, [= some s | cf <$> main]) / h := by
      simp only [div_eq_mul_inv]
      refine add_le_add ?_ (by simp [Finset.sum_mul])
      refine tsub_le_tsub le_rfl ?_
      have := ENNReal.rpow_sum_le_const_mul_sum_rpow
          (Finset.univ : Finset (Fin (qb i + 1)))
          (fun s => [= s | cf <$> main])
          (one_le_two)
      norm_num at this
      rw [mul_comm, ENNReal.inv_mul_le_iff]
      · refine le_trans this ?_
        simp [q]
      · simp [q]
      · simp [q]
    _ = 1 - acc ^ 2 / q + acc / h := rfl
    _ = 1 - acc * (acc / q - h⁻¹) := by
      rw [ENNReal.mul_sub]
      · simp [div_eq_mul_inv]
        ring_nf
        sorry -- Hypothesis that `h` is sufficiently large
      · simp [acc]


end OracleComp
