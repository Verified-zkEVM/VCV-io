/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Group.Basic
public import ToMathlib.Control.Monad.Indexed

/-!
# Graded Monads

A **graded monad** (also called a *parameterized monad* or, in some Haskell libraries, an
*indexed monad*) is a family of types `F : M → Type → Type`, indexed by a monoid `M`, equipped
with:
- `gpure : α → F 1 α`
- `gbind : F i α → (α → F j β) → F (i * j) β`

satisfying the monad laws up to the monoid laws on the index.

## Motivation

The primary motivation comes from interactive proof systems, where the `Prover` type is a graded
monad over the monoid `(ProtocolSpec, ++, [])` of protocol specifications (lists of interaction
rounds under concatenation). Sequential composition of provers concatenates their specs:
```
comp : Prover m A pSpec₁ → (A → Prover m B pSpec₂) → Prover m B (pSpec₁ ++ pSpec₂)
```

More generally, graded monads arise whenever `bind` accumulates a monoidal effect annotation:
effect systems, session types, resource tracking, etc.

## Relationship to other generalizations of monads

There are several related but distinct generalizations of monads in the literature:

- **Graded monad** (Katsumata 2014, Fujii–Katsumata–Melliès 2016): `F : M → Type → Type` over a
  monoid `M`. The index tracks accumulated effects. This is what we formalize here.

- **Atkey's indexed monad** (Atkey 2009, "Parameterised Notions of Computation"):
  `M : I → I → Type → Type` with `return : α → M i i α` and
  `bind : M i j α → (α → M j k β) → M i k β`. The two indices track pre/post-conditions,
  making this a monad in the functor category `[I, Type]`.

- **Relative monad** (Altenkirch–Chapman–Uustalu 2010/2015): relaxes the requirement that the
  monad be an endofunctor. Orthogonal to grading. See `ToMathlib.Control.Monad.Relative`.

The Haskell community sometimes uses "indexed monad" to mean what we call "graded monad".
The two concepts are related: a graded monad `F : M → Type → Type` can be viewed as an indexed
monad `M i j α := F (i⁻¹ * j) α` when `M` is a group, and conversely an indexed monad over a
set `I` with only identity transitions gives a graded monad over the trivial monoid.

## Implementation notes

Because the monoid laws (`one_mul`, `mul_one`, `mul_assoc`) are propositional rather than
definitional equalities, the graded monad laws involve `▸` (i.e., `Eq.mpr`) to transport terms
between propositionally-equal-but-definitionally-distinct types. This is the standard approach in
type-theoretic treatments of graded monads (see e.g., Orchard–Wadler–Eades 2019), and matches the
pattern used in `LawfulDijkstraMonad` (see `ToMathlib.Control.Monad.Dijkstra`).

## Main definitions

- `GradedMonad` — type class for graded monads
- `LawfulGradedMonad` — laws (using `▸` to cast along monoid identities/associativity)
- `GradedMonad.ofMonad` — every `Monad` is a `GradedMonad Unit` (trivial grading)
- `GradedMonadLift` — lifting from a base monad into a graded monad at the identity index
- `GradedMonadT` — graded monad transformers

## References

- Katsumata, S. (2014). *Parametric effect monads and semantics of effect systems*. POPL.
- Fujii, S., Katsumata, S., Melliès, P.-A. (2016). *Towards a formal theory of graded monads*.
  FOSSACS.
- Orchard, D., Wadler, P., Eades, H. (2019). *Unifying graded and parameterised monads*.
- Atkey, R. (2009). *Parameterised notions of computation*. JFP.
-/

@[expose] public section

universe u v w

instance : Monoid Unit where
  mul _ _ := ()
  one := ()
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-! ## Core definitions -/

/-- A graded monad over a monoid `M`. The type family `F : M → Type u → Type v` supports
`gpure` at the identity element and `gbind` that multiplies the indices.

Every ordinary `Monad` is a `GradedMonad Unit` (see `GradedMonad.ofMonad`). -/
class GradedMonad (M : Type w) [Monoid M] (F : M → Type u → Type v) where
  /-- Embed a pure value at the identity index. -/
  gpure {α : Type u} : α → F 1 α
  /-- Sequentially compose two graded computations, multiplying indices. -/
  gbind {α β : Type u} {i j : M} : F i α → (α → F j β) → F (i * j) β

export GradedMonad (gpure gbind)

namespace GradedMonad

variable {M : Type w} [Monoid M] {F : M → Type u → Type v} [GradedMonad M F]

/-- Graded functor map, derived from `gpure` and `gbind`.

Note: the result has index `i * 1` (not `i`), since `gbind` multiplies indices and `gpure`
contributes index `1`. A `LawfulGradedMonad` guarantees `i * 1 = i` propositionally. -/
def gmap {α β : Type u} {i : M} (f : α → β) (x : F i α) : F (i * 1) β :=
  gbind x (fun a => gpure (f a))

/-- Sequence two graded computations, discarding the first result. -/
def gseq {α β : Type u} {i j : M} (x : F i α) (y : F j β) : F (i * j) β :=
  gbind x (fun _ => y)

end GradedMonad

/-! ## Laws -/

/-- Laws for a graded monad: the monad laws hold up to the monoid identities and associativity,
using `▸` to transport across these propositional equalities.

Compare with `LawfulDijkstraMonad`, which uses the same `▸` pattern for the base monad laws. -/
class LawfulGradedMonad (M : Type w) [Monoid M] (F : M → Type u → Type v)
    [GradedMonad M F] : Prop where
  /-- Left identity: `gbind (gpure a) f` equals `f a` up to `1 * j = j`. -/
  gpure_gbind {α β : Type u} {j : M} (a : α) (f : α → F j β) :
    one_mul j ▸ gbind (gpure a) f = f a
  /-- Right identity: `gbind x gpure` equals `x` up to `i * 1 = i`. -/
  gbind_gpure {α : Type u} {i : M} (x : F i α) :
    mul_one i ▸ gbind x (gpure (M := M)) = x
  /-- Associativity: nested `gbind` reassociates up to `(i * j) * k = i * (j * k)`. -/
  gbind_assoc {α β γ : Type u} {i j k : M} (x : F i α)
      (f : α → F j β) (g : β → F k γ) :
    mul_assoc i j k ▸ gbind (gbind x f) g = gbind x (fun a => gbind (f a) g)

export LawfulGradedMonad (gpure_gbind gbind_gpure gbind_assoc)

attribute [simp] gpure_gbind gbind_gpure gbind_assoc

/-! ## Trivial grading: every monad is a graded monad over `Unit` -/

namespace GradedMonad

/-- Every `Monad` is a `GradedMonad` over the trivial monoid `Unit`,
with `gpure = pure` and `gbind = bind`. -/
instance ofMonad (m : Type u → Type v) [Monad m] :
    GradedMonad Unit (fun _ => m) where
  gpure := pure
  gbind x f := x >>= f

end GradedMonad

namespace LawfulGradedMonad

/-- The trivial grading of a lawful monad is a lawful graded monad. -/
instance ofLawfulMonad (m : Type u → Type v)
    [Monad m] [LawfulMonad m] :
    LawfulGradedMonad Unit (fun _ => m) where
  gpure_gbind a f := by simp [gpure, gbind]
  gbind_gpure x := by simp [gpure, gbind]
  gbind_assoc x f g := by simp [gbind, bind_assoc]

end LawfulGradedMonad

/-! ## Graded monad lifting -/

/-- Lifting from a base monad `m` into a graded monad `F` at the identity index.
This is the graded analogue of `MonadLift`: it embeds an `m`-computation as a graded
computation with trivial (identity) grade. -/
class GradedMonadLift (m : Type u → Type v) (M : Type w) [Monoid M]
    (F : M → Type u → Type v) where
  /-- Lift a base monad computation to the identity grade. -/
  glift {α : Type u} : m α → F 1 α

export GradedMonadLift (glift)

namespace GradedMonadLift

/-- The trivial grading has a trivial lift (the identity). -/
instance self (m : Type u → Type v) [Monad m] :
    GradedMonadLift m Unit (fun _ => m) where
  glift := id

end GradedMonadLift

/-! ## Graded monad transformers -/

/-- A graded monad transformer: given any monad `m`, provides a lifting from `m` into `t m` at the
identity index. The `GradedMonad M (t m)` instance is expected to be provided separately.

The canonical example is the prover transformer in interactive proof systems:
```
ProverT m pSpec α := m (Prover m α pSpec)
```
where `Prover m α pSpec` handles the protocol rounds in `pSpec`, the graded monad structure
comes from sequential composition (concatenating specs), and lifting from `m` embeds a base
computation at the empty spec. -/
class GradedMonadT (M : Type w) [Monoid M]
    (t : (Type u → Type v) → M → Type u → Type v) where
  /-- Lift a base monad computation into the graded monad transformer at the identity index. -/
  glift {m : Type u → Type v} [Monad m] {α : Type u} : m α → t m 1 α

/-! ## HEq variants of the laws

These are sometimes more convenient to work with than the `▸` versions, since `HEq` avoids
explicit transport. The two formulations are equivalent. -/

/-- `HEq`-based laws for graded monads. Equivalent to `LawfulGradedMonad` but avoids explicit
`▸` transport. -/
class LawfulGradedMonad' (M : Type w) [Monoid M] (F : M → Type u → Type v)
    [GradedMonad M F] : Prop where
  gpure_gbind {α β : Type u} {j : M} (a : α) (f : α → F j β) :
    HEq (gbind (gpure a) f) (f a)
  gbind_gpure {α : Type u} {i : M} (x : F i α) :
    HEq (gbind x (gpure (M := M))) x
  gbind_assoc {α β γ : Type u} {i j k : M} (x : F i α)
      (f : α → F j β) (g : β → F k γ) :
    HEq (gbind (gbind x f) g) (gbind x (fun a => gbind (f a) g))

namespace LawfulGradedMonad'

variable {M : Type w} [Monoid M] {F : M → Type u → Type v} [GradedMonad M F]

private theorem heq_of_subst_eq {α : Sort _} {P : α → Sort _} {a b : α}
    {x : P a} {y : P b} (h : a = b) (heq : h ▸ x = y) : HEq x y := by
  subst h; exact heq_of_eq heq

instance ofLawfulGradedMonad
    [h : LawfulGradedMonad M F] : LawfulGradedMonad' M F where
  gpure_gbind a f :=
    heq_of_subst_eq (P := fun m => F m _) (one_mul _) (LawfulGradedMonad.gpure_gbind a f)
  gbind_gpure x :=
    heq_of_subst_eq (P := fun m => F m _) (mul_one _) (LawfulGradedMonad.gbind_gpure x)
  gbind_assoc x f g :=
    heq_of_subst_eq (P := fun m => F m _) (mul_assoc _ _ _)
      (LawfulGradedMonad.gbind_assoc x f g)

end LawfulGradedMonad'

/-! ## Graded monad → Indexed monad (over a group)

When the grading monoid is a **group** `G`, every graded monad `F : G → Type → Type` gives rise
to an indexed monad `IxM i j α := F (i⁻¹ * j) α`.

The group structure is essential: `ireturn` needs `i⁻¹ * i = 1` (left inverse), and `ibind`
needs `(i⁻¹ * j) * (j⁻¹ * k) = i⁻¹ * k` (cancellation). For a mere monoid, this construction
is not available — graded monads and indexed monads are genuinely parallel generalizations. -/

namespace GradedMonad

variable {G : Type w} [Group G] {F : G → Type u → Type v} [GradedMonad G F]

/-- The indexed monad type family derived from a graded monad over a group:
`IxF F i j α := F (i⁻¹ * j) α`. -/
abbrev IxF (F : G → Type u → Type v) (i j : G) (α : Type u) : Type v :=
  F (i⁻¹ * j) α

/-- A graded monad over a group `G` gives rise to an indexed monad via
`IxF F i j α := F (i⁻¹ * j) α`. -/
instance toIndexedMonad : IndexedMonad G (IxF F) where
  ireturn {α i} a := by
    show F (i⁻¹ * i) α
    rw [inv_mul_cancel]
    exact gpure a
  ibind {α β i j k} x f := by
    show F (i⁻¹ * k) β
    rw [show i⁻¹ * k = i⁻¹ * j * (j⁻¹ * k) from by
      rw [mul_assoc, ← mul_assoc j, mul_inv_cancel, one_mul]]
    exact gbind x f

end GradedMonad
