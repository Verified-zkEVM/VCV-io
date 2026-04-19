/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Traces into a monoid

`Control.Trace ω X` is the type `X → ω` for any monoid `ω`.

It is the universal carrier of "stateless effectful trace" data:
each input contributes one element of a fixed monoid `ω`, and pointwise
multiplication (via `Pi.monoid`) gives `Trace ω X` itself the structure of a
monoid.  Nothing in this file requires a monad.

## Why a monoid, not a monad

Many bookkeeping / observation patterns share this exact shape:

* `QueryLog spec`             — `ω = List ((t : spec.Domain) × spec.Range t)`,
                                 i.e. the free monoid on indices,
* `QueryCount ι`              — `ω = ι → ℕ`, a commutative monoid under
                                 pointwise addition,
* `QueryCache spec`           — `ω = (t : spec.Domain) → Option (spec.Range t)`
                                 with at-most-once write semigroup,
* `BoundaryAction.emit`       — `ω = TraceList Δ.Out` (the polynomial-trace
                                 specialisation in `PFunctor/Trace.lean`),
* abstract cost functions     — `ω` any commutative monoid (e.g. `ℝ≥0`).

The monoid axioms are exactly what is needed to turn "one contribution per
input" into a meaningful aggregate over a sequence of inputs.

The companion file `ToMathlib/PFunctor/Trace.lean` specialises this at
`ω = FreeMonoid (Idx P)` for a polynomial functor `P`, recovering the
universal "log of P-events" trace, together with a universal property
`Trace P X → Control.Trace ω X` (`toMonoid`) coming from the free-monoid
universal property.

## Conventions

`Trace` is `@[reducible]` so that `Pi.monoid` and `Pi.commMonoid` apply
directly, and so that downstream definitions like `QueryLog` and `QueryCount`
can be exhibited as `Trace`-instances by `rfl`-clean abbreviations.

## References

* Bonchi, Di Lavore, Romàn — *Effectful Mealy machines and Kleisli
  categories*.
* Hancock, Setzer — *Interactive programs and weakly final coalgebras in
  dependent type theory*.
* Spivak, Niu — *Polynomial Functors: A Mathematical Theory of Interaction*,
  arXiv:2202.00534.
-/

@[expose] public section

universe u u' u'' v w

namespace Control

/--
`Trace ω X` is the type `X → ω` of stateless valuations from inputs `X` into
a monoid `ω`.  It inherits a monoid structure from `Pi.monoid`, with `1`
the constant trace and `*` the pointwise product.

See the module docstring for motivation and the catalogue of instances
(`QueryLog`, `QueryCount`, ...) it is intended to subsume.
-/
@[reducible] def Trace (ω : Type u) (X : Type v) : Type max u v := X → ω

namespace Trace

variable {ω : Type u} {ω' : Type u'} {ω'' : Type u''} {X Y Z : Type v}

/-- Pre-compose a trace with `f : Y → X`, giving a trace on `Y`. -/
def precomp (f : Y → X) (t : Trace ω X) : Trace ω Y := t ∘ f

/-- Post-compose a trace with a monoid homomorphism. -/
def map [MulOneClass ω] [MulOneClass ω'] (φ : ω →* ω') (t : Trace ω X) :
    Trace ω' X := φ ∘ t

/-! ### Pointwise behaviour of `precomp` -/

@[simp] theorem precomp_apply (f : Y → X) (t : Trace ω X) (y : Y) :
    precomp f t y = t (f y) := rfl

@[simp] theorem precomp_id (t : Trace ω X) : precomp id t = t := rfl

@[simp] theorem precomp_comp (g : Z → Y) (f : Y → X) (t : Trace ω X) :
    precomp g (precomp f t) = precomp (f ∘ g) t := rfl

@[simp] theorem precomp_one [One ω] (f : Y → X) :
    precomp f (1 : Trace ω X) = 1 := rfl

@[simp] theorem precomp_mul [Mul ω] (f : Y → X) (t s : Trace ω X) :
    precomp f (t * s) = precomp f t * precomp f s := rfl

/-! ### Pointwise behaviour of `map` -/

@[simp] theorem map_apply [MulOneClass ω] [MulOneClass ω']
    (φ : ω →* ω') (t : Trace ω X) (x : X) :
    map φ t x = φ (t x) := rfl

@[simp] theorem map_id [MulOneClass ω] (t : Trace ω X) :
    map (MonoidHom.id ω) t = t := rfl

@[simp] theorem map_comp [MulOneClass ω] [MulOneClass ω'] [MulOneClass ω'']
    (g : ω' →* ω'') (f : ω →* ω') (t : Trace ω X) :
    map (g.comp f) t = map g (map f t) := rfl

@[simp] theorem map_precomp [MulOneClass ω] [MulOneClass ω']
    (φ : ω →* ω') (f : Y → X) (t : Trace ω X) :
    map φ (precomp f t) = precomp f (map φ t) := rfl

@[simp] theorem map_one [MulOneClass ω] [MulOneClass ω'] (φ : ω →* ω') :
    map φ (1 : Trace ω X) = 1 := by
  funext x; exact φ.map_one

@[simp] theorem map_mul [MulOneClass ω] [MulOneClass ω'] (φ : ω →* ω')
    (t s : Trace ω X) :
    map φ (t * s) = map φ t * map φ s := by
  funext x; exact φ.map_mul _ _

/--
Bundle `map φ` as a monoid homomorphism on the trace monoid.

This is the manifest algebraic content of `map`: post-composing a trace with
a monoid hom is itself a monoid hom on the pointwise-monoid `Trace ω X`.
-/
@[simps]
def mapHom [Monoid ω] [Monoid ω'] (φ : ω →* ω') :
    Trace ω X →* Trace ω' X where
  toFun := map φ
  map_one' := map_one φ
  map_mul' := map_mul φ

end Trace

end Control
