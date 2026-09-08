/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLDSA.Arithmetic
public import LatticeCrypto.MLKEM.Arithmetic
public import LatticeCrypto.Falcon.Arithmetic
public import LatticeCrypto.Ring.Transform

/-!
# Generic Ring Smoke Checks

Compile-only smoke tests for the generic negacyclic ring architecture. Verifies
that the type-level wiring compiles for:

- A function-backed (`Fin n → Coeff`) alternative backend (`piBackend` /
  `piKernel` / `piRing` / `piSemantics`), ensuring the abstractions are not
  accidentally coupled to the vector representation.
- Each concrete scheme backend (`MLDSA`, `MLKEM`, `Falcon`), exercising
  negacyclic multiplication, quotient round-trips, norm evaluation, and
  integral-lift round-trips.

No runtime assertions — this file is purely a typecheck-time regression guard.
-/

@[expose] public section


namespace LatticeCrypto
namespace Smoke

/-- Function-backed alternative `PolyBackend` using `Fin n → Coeff` as carrier. -/
abbrev piBackend (Coeff : Type*) (n : Nat) : PolyBackend Coeff where
  Poly := Fin n → Coeff
  degree := n
  coeff := fun p i => p i
  build := fun f => f
  coeff_build := by
    intro f i
    rfl
  build_coeff := by
    intro p
    rfl

/-- Array kernel for the function-backed backend. -/
def piKernel (Coeff : Type*) [Zero Coeff] (n : Nat) :
    PolyKernel Coeff (piBackend Coeff n) where
  toArray := Array.ofFn
  ofArray := fun a i => a.getD i.val 0
  toArray_size := by
    intro p
    exact Array.size_ofFn
  coeff_ofArray := by
    intro a h i
    have hi : i.val < a.size := Nat.lt_of_lt_of_eq i.isLt h.symm
    simp [piBackend, hi]
  ofArray_toArray := by
    intro p
    funext i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    rw [dif_pos i.isLt, Option.getD_some]

/-- Bundled negacyclic ring over the function-backed backend. -/
abbrev piRing (Coeff : Type*) [CommRing Coeff] (n : Nat) :
    NegacyclicRing Coeff where
  backend := piBackend Coeff n
  kernel := piKernel Coeff n
  zero := fun _ => 0
  one  := fun i => if i.val = 0 then 1 else 0
  add := fun f g i => f i + g i
  sub := fun f g i => f i - g i
  neg := fun f i => -f i
  mul := negacyclicMulPure (piKernel Coeff n)
  add_coeff  _ _ _ := rfl
  sub_coeff  _ _ _ := rfl
  zero_coeff _     := rfl
  neg_coeff  _ _   := rfl

/-- Quotient semantics for the function-backed negacyclic ring (`n > 0`).
For `n = 0`, `X^0 + 1 = 2` and `mk(0) = 1` fails for general `CommRing`. -/
noncomputable def piSemantics (Coeff : Type*) [CommRing Coeff] {n : Nat} (hn : 0 < n) :
    NegacyclicRingSemantics (piRing Coeff n) where
  quotientOf := NegacyclicQuotient.ofBackend (piBackend Coeff n)
  zero_sound := by
    unfold NegacyclicQuotient.ofBackend NegacyclicQuotient.ofPolynomial PolyBackend.toPolynomial
    simp [piBackend, piRing, Finset.sum_const_zero, map_zero]
  one_sound := by
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial,
               PolyBackend.toPolynomial]
    simp only [map_sum]
    rw [Finset.sum_eq_single_of_mem ⟨0, hn⟩ (Finset.mem_univ _)]
    · simp [Polynomial.monomial_zero_left, map_one]
    · intro ⟨j, _⟩ _ hne
      simp only [Fin.mk.injEq, ne_eq] at hne
      simp [hne, map_zero]
  add_sound f g := by
    have hpoly : (piBackend Coeff n).toPolynomial ((piRing Coeff n).add f g) =
        (piBackend Coeff n).toPolynomial f + (piBackend Coeff n).toPolynomial g := by
      simp [PolyBackend.toPolynomial, piBackend, Finset.sum_add_distrib]
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, hpoly]
    exact map_add (Ideal.Quotient.mk _) _ _
  sub_sound f g := by
    have hpoly : (piBackend Coeff n).toPolynomial ((piRing Coeff n).sub f g) =
        (piBackend Coeff n).toPolynomial f - (piBackend Coeff n).toPolynomial g := by
      simp [PolyBackend.toPolynomial, piBackend, Finset.sum_sub_distrib]
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, hpoly]
    exact map_sub (Ideal.Quotient.mk _) _ _
  neg_sound f := by
    have hpoly : (piBackend Coeff n).toPolynomial ((piRing Coeff n).neg f) =
        -(piBackend Coeff n).toPolynomial f := by
      simp [PolyBackend.toPolynomial, piBackend, Finset.sum_neg_distrib]
    simp only [NegacyclicQuotient.ofBackend, NegacyclicQuotient.ofPolynomial, hpoly]
    exact map_neg (Ideal.Quotient.mk _) _
  mul_sound := by
    intro f g
    exact negacyclicMulPure_sound (piBackend Coeff n) (piKernel Coeff n) f g

/-! ### Typecheck-only roundtrip exercises

Each function below exercises a specific path through the generic ring layer for
a concrete scheme backend. They carry no runtime assertions — compilation success
is the test. -/

noncomputable def piQuotientRoundtrip {n : Nat} (hn : 0 < n) (f : (piRing (ZMod 17) n).Poly) :
    NegacyclicRingSemantics.Quotient (piSemantics (ZMod 17) hn) :=
  (piSemantics (ZMod 17) hn).quotientOf f

noncomputable def piNegacyclicRoundtrip (n : Nat) (f g : (piRing (ZMod 17) n).Poly) :
    (piRing (ZMod 17) n).Poly :=
  (piRing (ZMod 17) n).mul f g

noncomputable def mldsaQuotientRoundtrip (ops : MLDSA.NTTRingOps) (f : MLDSA.Rq) :
    MLDSA.Quotient :=
  MLDSA.quotientOfRq (ops.fromHat (ops.toHat f))

def mldsaNegacyclicRoundtrip (f g : MLDSA.Rq) : MLDSA.Rq :=
  MLDSA.negacyclicMul f g

def mldsaNormRoundtrip (f : MLDSA.Rq) : ℕ :=
  MLDSA.normOps.l2NormSq f

noncomputable def mlkemQuotientRoundtrip (ops : MLKEM.NTTRingOps) (f : MLKEM.Rq) :
    MLKEM.Quotient :=
  MLKEM.quotientOfRq (ops.fromHat (ops.toHat f))

def mlkemNegacyclicRoundtrip (f g : MLKEM.Rq) : MLKEM.Rq :=
  MLKEM.negacyclicMul f g

noncomputable def falconQuotientRoundtrip {n : ℕ} {hn : 0 < n} (ops : Falcon.NTTRingOps n)
    (f : Falcon.Rq n) : Falcon.Quotient hn :=
  Falcon.quotientOfRq (ops.fromHat (ops.toHat f))

def falconNegacyclicRoundtrip {n : ℕ} (f g : Falcon.Rq n) : Falcon.Rq n :=
  Falcon.negacyclicMul f g

def falconIntegralLiftRoundtrip {n : ℕ} (f : Falcon.IntPoly n) : Falcon.Rq n :=
  Falcon.integralLift n |>.toRq f

/-! ### Uniform sampling on scheme carriers

The generic `LatticeCrypto.Ring.Sampling` instances must be found through the scheme
aliases without unfolding the bundled ring. -/

example : Fintype MLKEM.Rq := inferInstance
example : SampleableType MLKEM.Rq := inferInstance
example : SampleableType MLKEM.Tq := inferInstance
example : SampleableType (MLKEM.RqVec 3) := inferInstance
example : SampleableType (MLKEM.TqVec 3) := inferInstance
example : SampleableType (MLKEM.TqMatrix 3 3) := inferInstance
example : SampleableType MLDSA.Rq := inferInstance
example : SampleableType (MLDSA.RqVec 4) := inferInstance
example : SampleableType (MLDSA.TqMatrix 4 4) := inferInstance
example {n : ℕ} : SampleableType (Falcon.Rq n) := inferInstance
example {n : ℕ} : SampleableType (Falcon.Tq n) := inferInstance

end Smoke
end LatticeCrypto
