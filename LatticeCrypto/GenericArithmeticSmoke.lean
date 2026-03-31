/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Ring
import LatticeCrypto.MLKEM.Ring
import LatticeCrypto.Falcon.Ring

/-!
# Generic Arithmetic Smoke Checks

This module provides compile-only instantiations of the generic negacyclic arithmetic
architecture for ML-DSA, ML-KEM, and Falcon.
-/


namespace LatticeCrypto
namespace Smoke

noncomputable def mldsaQuotientRoundtrip (ops : MLDSA.NTTRingOps) (f : MLDSA.Rq) :
    MLDSA.Quotient :=
  MLDSA.quotientOfRq (ops.fromHat (ops.toHat f))

def mldsaNegacyclicRoundtrip (f g : MLDSA.Rq) : MLDSA.Rq :=
  MLDSA.negacyclicOps.mul f g

def mldsaNormRoundtrip (f : MLDSA.Rq) : ℕ :=
  MLDSA.normOps.l2NormSq f

noncomputable def mlkemQuotientRoundtrip (ops : MLKEM.NTTRingOps) (f : MLKEM.Rq) :
    MLKEM.Quotient :=
  MLKEM.quotientOfRq (ops.fromHat (ops.toHat f))

def mlkemNegacyclicRoundtrip (f g : MLKEM.Rq) : MLKEM.Rq :=
  MLKEM.negacyclicOps.mul f g

noncomputable def falconQuotientRoundtrip {n : ℕ} (ops : Falcon.NTTRingOps n)
    (f : Falcon.Rq n) :
    Falcon.Quotient n :=
  Falcon.quotientOfRq (ops.fromHat (ops.toHat f))

def falconNegacyclicRoundtrip {n : ℕ} (f g : Falcon.Rq n) : Falcon.Rq n :=
  Falcon.negacyclicOps n |>.mul f g

def falconIntegralLiftRoundtrip {n : ℕ} (f : Falcon.IntPoly n) : Falcon.Rq n :=
  Falcon.integralLift n |>.toRq f

end Smoke
end LatticeCrypto
