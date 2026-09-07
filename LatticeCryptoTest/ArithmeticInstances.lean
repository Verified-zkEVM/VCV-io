/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import LatticeCrypto.MLDSA.Arithmetic
public import LatticeCrypto.MLKEM.Arithmetic

/-!
# Computable equality for lattice arithmetic carriers

Public imports must provide decidable equality for coefficient-domain polynomials,
transform-domain polynomials, and vectors without classical instance synthesis.
-/

public section

namespace LatticeCryptoTest.ArithmeticInstances

example : DecidableEq MLDSA.Rq := inferInstance
example : DecidableEq MLDSA.Tq := inferInstance
example : DecidableEq MLKEM.Rq := inferInstance
example : DecidableEq MLKEM.Tq := inferInstance
example (k : Nat) : DecidableEq (MLDSA.RqVec k) := inferInstance
example (k : Nat) : DecidableEq (MLKEM.RqVec k) := inferInstance

end LatticeCryptoTest.ArithmeticInstances
