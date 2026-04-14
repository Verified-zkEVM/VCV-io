/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Arithmetic
import LatticeCrypto.MLKEM.Arithmetic
import LatticeCrypto.Falcon.Arithmetic
import LatticeCrypto.Ring.Transform

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


namespace LatticeCrypto
namespace Smoke

/-- Function-backed alternative `PolyBackend` using `Fin n → Coeff` as carrier. -/
def piBackend (Coeff : Type*) (n : Nat) : PolyBackend Coeff where
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
    simp [piBackend]
  coeff_ofArray := by
    intro a h i
    have hi : i.val < a.size := Nat.lt_of_lt_of_eq i.isLt h.symm
    simp [piBackend, hi]
  ofArray_toArray := by
    intro p
    funext i
    simp

/-- Bundled negacyclic ring over the function-backed backend. -/
def piRing (Coeff : Type*) [CommRing Coeff] (n : Nat) :
    NegacyclicRing Coeff where
  backend := piBackend Coeff n
  kernel := piKernel Coeff n
  zero := fun _ => 0
  add := fun f g i => f i + g i
  sub := fun f g i => f i - g i
  neg := fun f i => -f i
  mul := negacyclicMulPure (piKernel Coeff n)

/-- Quotient semantics for the function-backed negacyclic ring. -/
noncomputable def piSemantics (Coeff : Type*) [CommRing Coeff] (n : Nat) :
    NegacyclicRingSemantics (piRing Coeff n) where
  quotientOf := NegacyclicQuotient.ofBackend (piBackend Coeff n)
  zero_sound := by
    unfold NegacyclicQuotient.ofBackend NegacyclicQuotient.ofPolynomial PolyBackend.toPolynomial
    simp [piBackend, piRing, Finset.sum_const_zero, map_zero]
    rfl
  add_sound := by
    intro f g
    unfold NegacyclicQuotient.ofBackend NegacyclicQuotient.ofPolynomial PolyBackend.toPolynomial
    simp only [piBackend, piRing, Finset.sum_add_distrib, map_add]
    rfl
  sub_sound := by
    intro f g
    unfold NegacyclicQuotient.ofBackend NegacyclicQuotient.ofPolynomial PolyBackend.toPolynomial
    simp only [piBackend, piRing, Finset.sum_sub_distrib, map_sub]
    rfl
  neg_sound := by
    intro f
    unfold NegacyclicQuotient.ofBackend NegacyclicQuotient.ofPolynomial PolyBackend.toPolynomial
    simp only [piBackend, piRing, Finset.sum_neg_distrib, map_neg]
    rfl
  mul_sound := by
    intro f g
    exact negacyclicMulPure_sound (piBackend Coeff n) (piKernel Coeff n) f g

/-! ### Typecheck-only roundtrip exercises

Each function below exercises a specific path through the generic ring layer for
a concrete scheme backend. They carry no runtime assertions — compilation success
is the test. -/

noncomputable def piQuotientRoundtrip (n : Nat) (f : (piRing (ZMod 17) n).Poly) :
    NegacyclicRingSemantics.Quotient (piSemantics (ZMod 17) n) :=
  (piSemantics (ZMod 17) n).quotientOf f

def piNegacyclicRoundtrip (n : Nat) (f g : (piRing (ZMod 17) n).Poly) :
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

noncomputable def falconQuotientRoundtrip {n : ℕ} (ops : Falcon.NTTRingOps n)
    (f : Falcon.Rq n) : Falcon.Quotient n :=
  Falcon.quotientOfRq (ops.fromHat (ops.toHat f))

def falconNegacyclicRoundtrip {n : ℕ} (f g : Falcon.Rq n) : Falcon.Rq n :=
  Falcon.negacyclicMul f g

def falconIntegralLiftRoundtrip {n : ℕ} (f : Falcon.IntPoly n) : Falcon.Rq n :=
  Falcon.integralLift n |>.toRq f

end Smoke
end LatticeCrypto
