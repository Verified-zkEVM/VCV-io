/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Indexed Monads (Atkey)

An **indexed monad** (Atkey 2009) is a family of types `M : I → I → Type → Type` equipped with:
- `ireturn : α → M i i α`
- `ibind : M i j α → (α → M j k β) → M i k β`

The two indices `i, j` track pre- and post-conditions (analogous to a state-indexed computation).
Unlike graded monads, the monad laws hold as exact equalities with no transport needed, since
the index composition is purely positional (the post-index of the first must match the pre-index
of the second).

## Relationship to graded monads

Indexed monads and graded monads are *parallel* generalizations of monads — neither subsumes the
other in general. However:

1. **Graded → Indexed (groups only)**: Given a graded monad `F : G → Type → Type` over a *group*
   `G`, we obtain an indexed monad `IxM i j α := F (i⁻¹ * j) α`. The group inverse is essential
   for constructing `ireturn` (which needs `i⁻¹ * i = 1`). See `GradedMonad.toIndexedMonad`.

2. **Trivial cases**: Every ordinary `Monad m` is both a `GradedMonad Unit (fun _ => m)` and an
   `IndexedMonad Unit (fun _ _ => m)`.

3. **Unification**: Both are special cases of the more general notion of *category-graded monads*
   (Fujii–Katsumata–Melliès 2016), where a graded monad is graded over a one-object category
   (monoid) and an indexed monad is graded over an indiscrete category.

## Main definitions

- `IndexedMonad` — type class for indexed monads
- `LawfulIndexedMonad` — the three monad laws (exact equalities, no transport needed)
- `instIndexedMonadOfMonad` — every `Monad` is an `IndexedMonad Unit`

## References

- Atkey, R. (2009). *Parameterised notions of computation*. JFP.
- Fujii, S., Katsumata, S., Melliès, P.-A. (2016). *Towards a formal theory of graded monads*.
  FOSSACS.
- Orchard, D., Wadler, P., Eades, H. (2019). *Unifying graded and parameterised monads*.
-/

@[expose] public section

universe u v

variable {I : Type*}

/-! ## Core definition -/

/-- An indexed monad (Atkey) over an index type `I`. The type family `M : I → I → Type u → Type v`
supports `ireturn` at diagonal indices and `ibind` that chains indices.

The indices track pre- and post-conditions: `M i j α` is a computation that starts in state `i`,
ends in state `j`, and produces a value of type `α`. -/
class IndexedMonad (I : Type*) (M : I → I → Type u → Type v) where
  /-- Embed a pure value at diagonal indices (state unchanged). -/
  ireturn {α : Type u} {i : I} : α → M i i α
  /-- Sequentially compose two indexed computations, chaining the intermediate index. -/
  ibind {α β : Type u} {i j k : I} : M i j α → (α → M j k β) → M i k β

export IndexedMonad (ireturn ibind)

namespace IndexedMonad

variable {M : I → I → Type u → Type v} [IndexedMonad I M]

/-- Indexed functor map, derived from `ireturn` and `ibind`. -/
def imap {α β : Type u} {i j : I} (f : α → β) (x : M i j α) : M i j β :=
  ibind x (fun a => ireturn (f a))

/-- Sequence two indexed computations, discarding the first result. -/
def iseq {α β : Type u} {i j k : I} (x : M i j α) (y : M j k β) : M i k β :=
  ibind x (fun _ => y)

end IndexedMonad

/-! ## Laws -/

/-- Laws for an indexed monad. Unlike graded monads, these are exact equalities — no transport
is needed because index composition is purely positional. -/
class LawfulIndexedMonad (I : Type*) (M : I → I → Type u → Type v)
    [IndexedMonad I M] : Prop where
  /-- Left identity. -/
  ireturn_ibind {α β : Type u} {i j : I} (a : α) (f : α → M i j β) :
    ibind (ireturn a) f = f a
  /-- Right identity. -/
  ibind_ireturn {α : Type u} {i j : I} (x : M i j α) :
    ibind x ireturn = x
  /-- Associativity. -/
  ibind_assoc {α β γ : Type u} {i j k l : I} (x : M i j α)
      (f : α → M j k β) (g : β → M k l γ) :
    ibind (ibind x f) g = ibind x (fun a => ibind (f a) g)

export LawfulIndexedMonad (ireturn_ibind ibind_ireturn ibind_assoc)

attribute [simp] ireturn_ibind ibind_ireturn ibind_assoc

/-! ## Trivial indexing: every monad is an indexed monad over `Unit` -/

/-- Every `Monad` is an `IndexedMonad` over `Unit`,
with `ireturn = pure` and `ibind = bind`. -/
instance instIndexedMonadOfMonad (m : Type u → Type v) [Monad m] :
    IndexedMonad Unit (fun _ _ => m) where
  ireturn := pure
  ibind x f := x >>= f

/-- The trivial indexing of a lawful monad is a lawful indexed monad. -/
instance instLawfulIndexedMonadOfLawfulMonad (m : Type u → Type v)
    [Monad m] [LawfulMonad m] :
    LawfulIndexedMonad Unit (fun _ _ => m) where
  ireturn_ibind a f := by simp [ireturn, ibind]
  ibind_ireturn x := by simp [ireturn, ibind]
  ibind_assoc x f g := by simp [ibind, bind_assoc]
