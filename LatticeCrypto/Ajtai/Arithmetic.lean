/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ring.Kernel
import LatticeCrypto.Ring.Norms

/-!
# Ajtai Arithmetic

This file provides the scoped notation shared by the Ajtai commitment layers
(`Simple` and `InnerOuter`): `R` for the canonical vector-backed negacyclic ring
`vectorNegacyclicRing (ZMod q) d` and `normOps` for its centered norm bundle
`zmodPolyNormOps q (vectorBackend (ZMod q) d)`. Both expand against the free
identifiers `q` and `d`, which must be in scope at the use site.

The gadget matrices built on top of this layer live in
`LatticeCrypto.Ajtai.Gadget`.
-/

open scoped BigOperators

universe u

namespace LatticeCrypto
namespace Ajtai

/-! ## Canonical ring notation

Scoped notation for the canonical vector-backed negacyclic ring and its centered
norm bundle, shared across the `Simple` and `InnerOuter` commitment layers. The
expansions reference the free identifiers `q` and `d`, resolved at the use site;
typical contexts carry `{q : ℕ} [NeZero q] [Fact (1 < q)] {d : ℕ} [NeZero d]`. -/

set_option quotPrecheck false in
set_option hygiene false in
/-- The canonical vector-backed negacyclic ring `ZMod q[X]/(Xᵈ + 1)`. -/
scoped notation:max "R" => vectorNegacyclicRing (ZMod q) d

set_option quotPrecheck false in
set_option hygiene false in
/-- The canonical centered-norm bundle on `R`. -/
scoped notation:max "normOps" => zmodPolyNormOps q (vectorBackend (ZMod q) d)

/-
TODO add the proper arithmetic primitves for ajtai commitments here, and also the Hachi/Greyhound
primitives for Inner-Outer Ajtai commitments.

Add more general arithmetic primitive(s) for the Simple and Hiding Atjati commitments and (a) more
specialized one(s) for the Inner-Outer Ajtai commitment (if necessary, which it probably is).
For the inner-outer commitment orientate on the Hachi parameters.
-/

end Ajtai
end LatticeCrypto
