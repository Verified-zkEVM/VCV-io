/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.VectorCommRing
import LatticeCrypto.Ring.Norms
import Mathlib.Data.Nat.Prime.Basic

/-!
# Invertibility of Short Elements (Lyubashevsky–Seiler)

This file records the Lyubashevsky–Seiler "short elements are invertible" result for
the canonical vector-backed negacyclic ring `vectorNegacyclicRing (ZMod q) d`,
specialized to the parameter regime used by Greyhound/Hachi.

The statement is Corollary 1.2 of Lyubashevsky–Seiler, "Short, Invertible Elements in
Partially Splitting Cyclotomic Rings" (EUROCRYPT 2018), as recalled in Lemma 3 of the
Hachi paper (Nguyen–O'Rourke–Zhang): for a prime `q ≡ 5 (mod 8)` and power-of-two
degree `d`, every nonzero element of `R_q = ZMod q[X]/(Xᵈ + 1)` whose centered
Euclidean norm is below `√q` is a unit.

The proof is a genuine piece of algebraic number theory — it goes through the
factorization of `Xᵈ + 1 mod q` into two irreducible degree-`d/2` factors (so
`R_q ≅ 𝔽_{q^{d/2}} × 𝔽_{q^{d/2}}`), realizes each maximal ideal as an ideal lattice of
determinant `q^{d/2}`, and lower-bounds its minimum distance by `√(φ(2d))/s₁(2d) ·
q^{1/2} = q^{1/2}` using the singular value `s₁(2d) = √d` of the cyclotomic Vandermonde
matrix. None of this lattice/embedding-norm machinery is currently available in
Mathlib in directly usable form, so the result is recorded here with `sorry` and
discharged downstream; see `docs`/the security files for how it replaces the
`isUnitLike → IsUnit` assumption.
-/

open scoped BigOperators

namespace LatticeCrypto

variable {q : ℕ} [NeZero q] [Fact (1 < q)] {d : ℕ} [NeZero d]

/-- **Lyubashevsky–Seiler: short elements are invertible** (LS18, Corollary 1.2;
Hachi, Lemma 3). For a prime `q ≡ 5 (mod 8)` and power-of-two degree `d`, a nonzero
element of `vectorNegacyclicRing (ZMod q) d` whose centered squared `ℓ₂` norm is below
`q` (i.e. centered `ℓ₂` norm below `√q`) is a unit of the ring.

The norm here is the centered Euclidean norm `zmodPolyNormOps q (vectorBackend (ZMod q)
d)`; `‖c‖₂² < q` is exactly the LS bound `‖c‖ < q^{1/2}`. -/
theorem isUnit_of_l2NormSq_lt
    (hq : Nat.Prime q) (hq5 : q % 8 = 5) (hd : ∃ α : ℕ, d = 2 ^ α)
    {c : (vectorNegacyclicRing (ZMod q) d).Poly}
    (hc0 : 0 < ‖c‖⟪zmodPolyNormOps q (vectorBackend (ZMod q) d)⟫₂²)
    (hclt : ‖c‖⟪zmodPolyNormOps q (vectorBackend (ZMod q) d)⟫₂² < q) :
    IsUnit c := by
  sorry

/-- Invertibility in the `ℓ₁` form used by the Greyhound/Hachi weak-binding extractor: a
nonzero challenge with `‖c‖₁ ≤ κ` is a unit whenever `κ² < q`. This holds because then the
centered Euclidean norm satisfies `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q`, so `isUnit_of_l2NormSq_lt`
applies. (Hachi's Lemma 8 uses the analogous `‖c‖∞`/`ℓ₂` bound on challenge differences.) -/
theorem isUnit_of_l1Norm_le {kappa : ℕ}
    (hq : Nat.Prime q) (hq5 : q % 8 = 5) (hd : ∃ α : ℕ, d = 2 ^ α)
    {c : (vectorNegacyclicRing (ZMod q) d).Poly}
    (hpos : 0 < ‖c‖⟪zmodPolyNormOps q (vectorBackend (ZMod q) d)⟫₁)
    (hle : ‖c‖⟪zmodPolyNormOps q (vectorBackend (ZMod q) d)⟫₁ ≤ kappa)
    (hκ : kappa ^ 2 < q) : IsUnit c := by
  refine isUnit_of_l2NormSq_lt hq hq5 hd (l2NormSq_pos_of_l1Norm_pos hpos) ?_
  calc l2NormSq c ≤ l1Norm c ^ 2 := l2NormSq_le_l1Norm_sq c
    _ ≤ kappa ^ 2 := Nat.pow_le_pow_left hle 2
    _ < q := hκ

end LatticeCrypto
