/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToMathlib.MeasureTheory.DiscreteInstances
public import ToMathlib.Probability.UniformOn
public import ToMathlib.General
public import Examples.OneTimePad.Basic
public import VCVio.CryptoFoundations.Asymptotics.PathSemantics
public import VCVio.CryptoFoundations.SymmEncAlg.Measure
public import Mathlib.Data.LawfulXor.Equiv

/-!
# A measure-native fair-coin one-time pad

This file is an end-to-end feasibility test for the computational-complexity stack. The key
sampler is fully syntactic `OracleComp coinSpec` code with exactly one oracle interaction per key
bit. Its semantics is selected independently by `fairCoinMeasureSpec`, which assigns the native
uniform Mathlib measure to every coin answer.

The proof deliberately establishes equalities of whole measures. Independent draws are related
to Mathlib's product measure, finite uniformity is transported through explicit bijections, and
the resulting encryption scheme satisfies measure-level correctness and perfect secrecy. Query
cost is obtained from PolyFun's typed paths before any probability semantics is applied.

`CoinBitVecFamily.IsPPTByUnder` records the remaining backend-relative uniform-PPT obligation.
The exact path and measure theorems below do not manufacture a uniform machine implementation for
the variable-width family.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open scoped ENNReal
open PFunctor
open PFunctor.DynSystem.DynComputation

namespace oneTimePad

/-! ## Explicit fair-bit sampling -/

/-- Native fair-coin measure semantics for the polynomial interface underlying `coinSpec`.

This is an explicit semantic choice rather than an instance inferred from finiteness. Callers may
replace it with another `IsMeasureSpec` when studying a biased or otherwise concrete source. -/
@[instance_reducible]
noncomputable def fairCoinMeasureSpec : coinSpec.toPFunctor.IsMeasureSpec :=
  PFunctor.IsMeasureSpec.uniformOfFintypeInhabited _

attribute [local instance] fairCoinMeasureSpec

/-- One syntactic query to the fair-coin interface. -/
def fairCoin : OracleComp coinSpec Bool :=
  PFunctor.FreeM.lift ()

/-- Sample an `n`-coordinate Boolean function using one explicit query per coordinate. -/
def coinVector : (n : ℕ) → OracleComp coinSpec (Fin n → Bool)
  | 0 => pure Fin.elim0
  | n + 1 => PFunctor.FreeM.liftBind () fun bit =>
      PFunctor.FreeM.map (Fin.cons bit) (coinVector n)

/-- Interpret Boolean coordinates as a little-endian fixed-width bit vector. -/
def bitVecOfFnLE {n : ℕ} (bits : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast List.length_ofFn

/-- Reading a coordinate after little-endian packing recovers that coordinate. -/
@[simp]
theorem bitVecOfFnLE_getLsb {n : ℕ} (bits : Fin n → Bool) (index : Fin n) :
    (bitVecOfFnLE bits).getLsb index = bits index := by
  unfold bitVecOfFnLE
  change
    (BitVec.cast List.length_ofFn (BitVec.ofBoolListLE (List.ofFn bits))).getLsbD
      index.val = bits index
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, index.isLt]

/-- Interpret an explicitly sampled Boolean vector as a little-endian `BitVec`. -/
def coinBitVec (n : ℕ) : OracleComp coinSpec (BitVec n) :=
  PFunctor.FreeM.map bitVecOfFnLE (coinVector n)

/-- `bitVecOfFnLE` is injective because every input coordinate can be read back. -/
private theorem bitVecOfFnLE_injective (n : ℕ) :
    Function.Injective (bitVecOfFnLE : (Fin n → Bool) → BitVec n) := by
  intro lhs rhs heq
  funext index
  have hbit := congrArg (fun value : BitVec n ↦ value.getLsb index) heq
  simpa only [bitVecOfFnLE_getLsb] using hbit

/-- `bitVecOfFnLE` is a bijection between coordinates and fixed-width bit vectors. -/
private theorem bitVecOfFnLE_bijective (n : ℕ) :
    Function.Bijective (bitVecOfFnLE : (Fin n → Bool) → BitVec n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨bitVecOfFnLE_injective n, by simp⟩

/-! ## Exact syntactic query accounting -/

/-- Transporting a typed path along an equality preserves its length. -/
private theorem pathLength_transport {P : PFunctor} {α : Type}
    {source target : PFunctor.FreeM P α} (h : source = target)
    (path : PFunctor.FreeM.Path source) :
    PFunctor.FreeM.Path.length source path =
      PFunctor.FreeM.Path.length target (h ▸ path) := by
  subst target
  rfl

/-- Every complete typed path through `coinVector n` contains exactly `n` queries. -/
theorem coinVector_path_length : (n : ℕ) →
    (path : PFunctor.FreeM.Path (coinVector n).toFreeM) →
    PFunctor.FreeM.Path.length (coinVector n).toFreeM path = n
  | 0, path => by
      change PFunctor.FreeM.Path.length (PFunctor.FreeM.pure Fin.elim0) path = 0
      exact PFunctor.FreeM.Path.length_pure Fin.elim0 path
  | n + 1, path => by
      let expanded : PFunctor.FreeM coinSpec.toPFunctor (Fin (n + 1) → Bool) :=
        PFunctor.FreeM.liftBind () fun bit =>
          PFunctor.FreeM.map (Fin.cons bit) (coinVector n).toFreeM
      have hprogram : (coinVector (n + 1)).toFreeM = expanded := by
        rw [coinVector]
      let path' := hprogram ▸ path
      calc
        PFunctor.FreeM.Path.length (coinVector (n + 1)).toFreeM path =
            PFunctor.FreeM.Path.length expanded path' :=
          pathLength_transport hprogram path
        _ = n + 1 := by
          dsimp only [expanded] at path'
          rcases path' with ⟨bit, tail⟩
          change Bool at bit
          change PFunctor.FreeM.Path
            (PFunctor.FreeM.map (@Fin.cons n (fun _ ↦ Bool) bit)
              (coinVector n).toFreeM) at tail
          change PFunctor.FreeM.Path.length
            (PFunctor.FreeM.map (@Fin.cons n (fun _ ↦ Bool) bit)
              (coinVector n).toFreeM) tail + 1 = n + 1
          rw [← PFunctor.FreeM.Path.length_pullMap]
          rw [coinVector_path_length n]

/-- Every complete typed path through `coinBitVec n` contains exactly `n` queries. -/
theorem coinBitVec_path_length (n : ℕ)
    (path : PFunctor.FreeM.Path (coinBitVec n).toFreeM) :
    PFunctor.FreeM.Path.length (coinBitVec n).toFreeM path = n := by
  let mapped := PFunctor.FreeM.map bitVecOfFnLE (coinVector n).toFreeM
  have hprogram : (coinBitVec n).toFreeM = mapped := rfl
  let path' := hprogram ▸ path
  calc
    PFunctor.FreeM.Path.length (coinBitVec n).toFreeM path =
        PFunctor.FreeM.Path.length mapped path' := pathLength_transport hprogram path
    _ = PFunctor.FreeM.Path.length (coinVector n).toFreeM
        (PFunctor.FreeM.Path.pullMap bitVecOfFnLE (coinVector n).toFreeM path') := by
      symm
      exact PFunctor.FreeM.Path.length_pullMap bitVecOfFnLE (coinVector n).toFreeM path'
    _ = n := coinVector_path_length n _

/-- The query-count law of the explicit key sampler is concentrated exactly at `n`. -/
theorem queryCountMeasure_coinBitVec_eq_dirac (n : ℕ) :
    PFunctor.FreeM.queryCountMeasure (coinBitVec n).toFreeM = Measure.dirac n :=
  PFunctor.FreeM.queryCountMeasure_eq_dirac_of_length_eq
    (coinBitVec n).toFreeM n (coinBitVec_path_length n)

/-- The expected number of interactions in the explicit key sampler is exactly `n`. -/
theorem expectedQueryCount_coinBitVec_eq (n : ℕ) :
    PFunctor.FreeM.expectedQueryCount (coinBitVec n).toFreeM = (n : ℝ≥0∞) :=
  PFunctor.FreeM.expectedQueryCount_eq_of_length_eq
    (coinBitVec n).toFreeM n (coinBitVec_path_length n)

/-! ## Uniform measure semantics -/

/-- One fair-coin query denotes the native uniform measure on `Bool`. -/
@[simp]
theorem denote_fairCoin :
    PFunctor.FreeM.denote fairCoin.toFreeM = uniformOn (Set.univ : Set Bool) := by
  change PFunctor.FreeM.denote
    (PFunctor.FreeM.lift (P := coinSpec.toPFunctor) ()) = _
  exact PFunctor.FreeM.denote_lift (P := coinSpec.toPFunctor) ()

/-- The successor sampler is a relabelling of a pair of independent samplers. -/
private theorem coinVector_succ_eq_map_pair (n : ℕ) :
    (coinVector (n + 1)).toFreeM =
      PFunctor.FreeM.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
        (PFunctor.FreeM.bind fairCoin.toFreeM fun bit =>
          PFunctor.FreeM.bind (coinVector n).toFreeM fun tail =>
            pure (bit, tail)) := by
  rw [coinVector]
  unfold fairCoin
  change
    PFunctor.FreeM.liftBind ()
        (fun bit => PFunctor.FreeM.map (Fin.cons bit) (coinVector n).toFreeM) =
      PFunctor.FreeM.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
        (PFunctor.FreeM.liftBind () fun bit =>
          PFunctor.FreeM.bind (coinVector n).toFreeM fun tail =>
            pure (bit, tail))
  rw [PFunctor.FreeM.map_liftBind]
  have hnext :
      (fun bit : Bool => PFunctor.FreeM.map (Fin.cons bit) (coinVector n).toFreeM) =
        fun bit => PFunctor.FreeM.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
          (PFunctor.FreeM.bind (coinVector n).toFreeM fun tail =>
            pure (bit, tail)) := by
    funext bit
    have hpair :
        PFunctor.FreeM.bind (coinVector n).toFreeM
            (fun tail => pure (bit, tail)) =
          PFunctor.FreeM.map (Prod.mk bit) (coinVector n).toFreeM := by
      change PFunctor.FreeM.bind (coinVector n).toFreeM (pure ∘ Prod.mk bit) = _
      exact PFunctor.FreeM.bind_pure_comp (Prod.mk bit) (coinVector n).toFreeM
    rw [hpair]
    rw [← PFunctor.FreeM.comp_map]
    rfl
  exact congrArg
    (PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) ()) hnext

/-- Explicit independent coin sampling is uniform on Boolean vectors. -/
theorem denote_coinVector_eq_uniform (n : ℕ) :
    PFunctor.FreeM.denote (coinVector n).toFreeM =
      uniformOn (Set.univ : Set (Fin n → Bool)) := by
  induction n with
  | zero =>
      apply Measure.ext_of_singleton
      intro value
      have hvalue : value = Fin.elim0 := funext fun index ↦ index.elim0
      subst value
      simp [coinVector]
  | succ n ih =>
      rw [coinVector_succ_eq_map_pair]
      rw [PFunctor.FreeM.denote_map_of_discrete (P := coinSpec.toPFunctor)]
      calc
        Measure.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
            (PFunctor.FreeM.denote
              (PFunctor.FreeM.bind fairCoin.toFreeM fun bit =>
                PFunctor.FreeM.bind (coinVector n).toFreeM fun tail =>
                  pure (bit, tail))) =
            Measure.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
              ((PFunctor.FreeM.denote fairCoin.toFreeM).prod
                (PFunctor.FreeM.denote (coinVector n).toFreeM)) := by
          exact congrArg (Measure.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)))
            (PFunctor.FreeM.denote_bind_bind_prod_mk_eq_prod
              (P := coinSpec.toPFunctor) fairCoin.toFreeM (coinVector n).toFreeM)
        _ = Measure.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
              ((uniformOn (Set.univ : Set Bool)).prod
                (uniformOn (Set.univ : Set (Fin n → Bool)))) := by
          rw [denote_fairCoin, ih]
        _ = Measure.map (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
              (uniformOn (Set.univ : Set (Bool × (Fin n → Bool)))) := by
          rw [uniformOn_univ_prod]
        _ = uniformOn (Set.univ : Set (Fin (n + 1) → Bool)) :=
          map_uniformOn_univ_of_bijective Measurable.of_discrete
            (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)).bijective

/-- The explicit `n`-coin key generator is uniform on `BitVec n`. -/
theorem denote_coinBitVec_eq_uniform (n : ℕ) :
    PFunctor.FreeM.denote (coinBitVec n).toFreeM =
      uniformOn (Set.univ : Set (BitVec n)) := by
  change PFunctor.FreeM.denote
    (PFunctor.FreeM.map bitVecOfFnLE (coinVector n).toFreeM) = _
  rw [PFunctor.FreeM.denote_map_of_discrete (P := coinSpec.toPFunctor),
    denote_coinVector_eq_uniform]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete
    (bitVecOfFnLE_bijective n)

/-- The primary measure semantics of the explicit key generator is the uniform measure: the
`𝒟[…]` reading of `denote_coinBitVec_eq_uniform`. -/
theorem evalDist_coinBitVec (n : ℕ) :
    𝒟[coinBitVec n] = uniformOn (Set.univ : Set (BitVec n)) :=
  denote_coinBitVec_eq_uniform n

/-- Every key is drawn with probability `(2 ^ n)⁻¹`. -/
theorem evalDist_coinBitVec_apply_singleton (n : ℕ) (key : BitVec n) :
    𝒟[coinBitVec n] {key} = (2 ^ n : ℝ≥0∞)⁻¹ := by
  simp [evalDist_coinBitVec]

/-- The explicit key generator never fails: its denotation carries total mass one. -/
theorem evalDist_coinBitVec_apply_univ (n : ℕ) : 𝒟[coinBitVec n] Set.univ = 1 := by
  simp [evalDist_coinBitVec]

/-! ## A measure-level one-time pad -/

/-- The one-time pad whose key sampler uses one explicit coin query per key bit. -/
def coinOneTimePad (sp : ℕ) :
    SymmEncAlg (OracleComp coinSpec) (BitVec sp) (BitVec sp) (BitVec sp) :=
  oneTimePadOfKeygen sp (coinBitVec sp)

/-- Encryption followed by decryption has the Dirac law at the original message. -/
theorem coinOneTimePad_measureComplete (sp : ℕ) :
    (coinOneTimePad sp).measureComplete ProbabilitySemantics.freeM := by
  intro message
  have hprogram : (coinOneTimePad sp).CompleteExp message =
      PFunctor.FreeM.map (fun _ : BitVec sp ↦ some message) (coinBitVec sp).toFreeM := by
    simp [SymmEncAlg.CompleteExp, coinOneTimePad, monad_norm]
  rw [hprogram]
  change PFunctor.FreeM.denote
    (PFunctor.FreeM.map (fun _ : BitVec sp ↦ some message) (coinBitVec sp).toFreeM) = _
  rw [PFunctor.FreeM.denote_map_of_discrete (P := coinSpec.toPFunctor),
    denote_coinBitVec_eq_uniform]
  rw [Measure.map_const]
  simp

/-- For every fixed message, ciphertext is uniform on the full ciphertext space. -/
theorem denote_coinOneTimePad_cipherGivenMsg_eq_uniform
    (sp : ℕ) (message : BitVec sp) :
    PFunctor.FreeM.denote
        ((coinOneTimePad sp).PerfectSecrecyCipherGivenMsgExp message).toFreeM =
      uniformOn (Set.univ : Set (BitVec sp)) := by
  have hprogram : (coinOneTimePad sp).PerfectSecrecyCipherGivenMsgExp message =
      PFunctor.FreeM.map (fun key : BitVec sp ↦ key ^^^ message)
        (coinBitVec sp).toFreeM := by
    simp [SymmEncAlg.PerfectSecrecyCipherGivenMsgExp, coinOneTimePad, monad_norm]
  rw [hprogram]
  change PFunctor.FreeM.denote
    (PFunctor.FreeM.map (fun key : BitVec sp ↦ key ^^^ message)
      (coinBitVec sp).toFreeM) = _
  rw [PFunctor.FreeM.denote_map_of_discrete (P := coinSpec.toPFunctor),
    denote_coinBitVec_eq_uniform]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete
    (xor_left_involutive message).bijective

/-- The explicit-coin one-time pad is perfectly secret in measure semantics. -/
theorem coinOneTimePad_measurePerfectSecrecyAt (sp : ℕ) :
    (coinOneTimePad sp).measurePerfectSecrecyAt ProbabilitySemantics.freeM :=
  (coinOneTimePad sp).measurePerfectSecrecyAt_of_constant ProbabilitySemantics.freeM
    (uniformOn (Set.univ : Set (BitVec sp)))
    (denote_coinOneTimePad_cipherGivenMsg_eq_uniform sp)

/-! ## Uniform strict-PPT boundary -/

/-- The packed security family of explicit-coin OTP key generators. -/
def coinBitVecFamily (n : ℕ) (_ : Unit) : OracleComp coinSpec (BitVec n) :=
  coinBitVec n

namespace CoinBitVecFamily

/-- The backend-relative uniform-PPT proposition for `coinBitVecFamily`.

An inhabitant must provide one realization of the packed family and one polynomial bounding all
security parameters and Boolean response paths. Pointwise witnesses do not inhabit this
proposition. -/
def IsPPTByUnder
    {C : PFunctor.StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq
      (OracleComp.SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).Domain]
    (Q : PFunctor.QuantitativeStepClass C)
    (bd : Boundary C
      (OracleComp.SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).toPFunctor
      (OracleComp.SecurityFamily.Input (fun _ : ℕ ↦ Unit))
      (OracleComp.SecurityFamily.Output (fun n : ℕ ↦ BitVec n)))
    {label : Type}
    (contract : OracleComp.Complexity.OracleContract Q bd.interface label) : Prop :=
  OracleComp.Complexity.SecurityFamily.IsCoinPPTByUnder
    Q bd contract coinBitVecFamily

end CoinBitVecFamily

end oneTimePad
