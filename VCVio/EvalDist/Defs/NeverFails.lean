/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.EvalDist.Defs.HasFinSupport

/-!
# Computations that Never Fail

This file defines a predicate-as-typeclass stating that a probabilistic computation never
produces failure mass, together with lemmas for how the property behaves under common
monadic combinators.

Definitions are given relative to a canonical embedding `evalDist : m →ᵐ SPMF` provided by
`[HasSPMF m]`. We write

  `Pr[⊥ | mx] := (evalDist mx).run none`

so “never fails” means exactly `Pr[⊥ | mx] = 0`.

Design notes
- We keep a thin `NeverFail` typeclass so that trivial cases synthesize automatically
  (e.g. `pure`, `map`).
- We do not register a `bind` instance. Instead, we provide two lemmas:
  1) `bind_of_mem_support`: precise and recommended. It needs `neverFail (my x)` only for
     `x ∈ support mx`.
  2) `bind_of_forall`: stronger sufficient condition obtained by instantiating (1) with
     a trivial restriction.
- This avoids encoding term-dependent assumptions into typeclass search, while keeping
  ergonomic instances for the easy cases.
-/

universe u v w

namespace HasSPMF

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/--
`NeverFail mx` states that the computation `mx : m α` has zero probability of failure,
equivalently the mass of `(evalDist mx)` at `none` is `0`.

Formally: `NeverFail mx` iff `Pr[⊥ | mx] = 0`.

Remarks:
- This class is a predicate (Prop-valued). It does not add data.
- Use the lemmas in this file (e.g. `bind_of_mem_support`) to transport the property through
  monadic structure. We intentionally avoid a `bind` instance, as the natural condition depends
  on the support of the left-hand side.
-/
class NeverFail {α : Type u} {m : Type u → Type v} [Monad m]
    [HasSPMF m] (mx : m α) : Prop where
  mk :: probFailure_eq_zero : Pr[⊥ | mx] = 0

export NeverFail (probFailure_eq_zero)

namespace NeverFail

section spmf

variable [HasSPMF m]

@[simp]
lemma of_probFailure_eq_zero (mx : m α) (h : Pr[⊥ | mx] = 0) : NeverFail mx :=
  { probFailure_eq_zero := h }

/--
If `mx` is a pure return, it never fails.
This follows since `evalDist (pure x)` is the Dirac distribution on `some x`.
-/
@[simp]
instance instPure {x} : NeverFail (pure x : m α) where
  probFailure_eq_zero := by simp [probFailure]

variable [LawfulMonad m]

/--
Precise bind lemma: if `mx` never fails and for all `x` in the support of `mx` the continuation
`my x` never fails, then the whole bind never fails.

Sketch: using `evalDist_bind` and the identity

  `Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑ x, Pr[= x | mx] * Pr[⊥ | my x]`,

the first term vanishes by `NeverFail mx`, while for `x ∉ support mx` the coefficient
`Pr[= x | mx]` is `0`, and for `x ∈ support mx` the second factor vanishes by hypothesis.
Hence the sum is `0`.
-/
lemma bind_of_mem_support {mx : m α} {my : α → m β}
    [hx : NeverFail mx] (hy : ∀ x ∈ support mx, NeverFail (my x)) :
    NeverFail (mx >>= my) where
  probFailure_eq_zero := by sorry

/--
Weak bind lemma: if the right-hand side never fails for every possible input (`∀ x`),
then the bind never fails.

This is a convenience corollary of `bind_of_mem_support`; it is often easy to apply when
`my` is uniform in its input (e.g. ignores it) or is known to be never-failing globally.
-/
lemma bind_of_forall {mx : m α} {my : α → m β}
    [hx : NeverFail mx] [hy : ∀ x, NeverFail (my x)] :
    NeverFail (mx >>= my) := bind_of_mem_support (hx := hx) (fun x _ => hy x)

/--
Mapping a value through a total function preserves `NeverFail`.
-/
@[simp]
instance instMap {mx : m α} [h : NeverFail mx] (f : α → β) :
    NeverFail (f <$> mx) := by
  simp [map_eq_bind_pure_comp, bind_of_forall]

/-- If both the function computation and the argument computation never fail,
then their applicative sequencing also never fails. -/
@[simp]
instance instSeq {mf : m (α → β)} {mx : m α} [hf : NeverFail mf] [hx : NeverFail mx] :
    NeverFail (mf <*> mx) := by
  -- `mf <*> mx = mf >>= fun f => f <$> mx`, and mapping preserves `NeverFail` given `hx`.
  simpa [seq_eq_bind_map] using
    (bind_of_forall (mx := mf) (my := fun f => f <$> mx)
      (hx := hf) (hy := fun f => by simp))

/-- If `mx` and `my` never fail, then `mx <* my` never fails. -/
@[simp]
instance instSeqLeft {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx <* my) := by
  simp [seqLeft_eq]

/-- If `mx` and `my` never fail, then `mx *> my` never fails. -/
@[simp]
instance instSeqRight {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx *> my) := by
  simp [seqRight_eq]

end spmf

/-- A computation in a monad with `HasPMF` that naturally embeds into `HasSPMF`
would never fails -/
instance [HasPMF m] (mx : m α) : NeverFail mx where
  probFailure_eq_zero := by
    simp [probFailure, HasPMF.instHasSPMF, OptionT.run, evalDist, OptionT.mk]

end NeverFail

end HasSPMF
