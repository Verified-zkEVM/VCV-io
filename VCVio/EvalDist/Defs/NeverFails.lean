/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.EvalDist.Defs.AlternativeMonad
import VCVio.EvalDist.Monad.Seq

/-!
# Computations that Never Fail

This file defines a predicate-as-typeclass stating that a probabilistic computation never
produces failure mass, together with lemmas for how the property behaves under common
monadic combinators.

Given a `HasEvalSPMF m` instance and a computation `mx : m α` in that monad, `NeverFail mx` means
that `Pr[⊥ | mx] = 0`, i.e. that the computation never fails.

Defined as a typeclass to allow it to be synthesized automatically in certain cases.
However we don't include any instances for `bind` as this blows up the search space.
Instances involving `bind` should be added manually as needed.

The existence of a `HasEvalPMF m` instance implies that `NeverFail mx` holds for any computaiton
in the monad, since the `PMF` doesn't allow any probability of failing.
-/

universe u v w

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
    [HasEvalSPMF m] (mx : m α) : Prop where
  mk :: probFailure_eq_zero : Pr[⊥ | mx] = 0

export NeverFail (probFailure_eq_zero)

attribute [simp] probFailure_eq_zero
attribute [aesop safe apply] NeverFail.mk

/-- Version of `probFailure_eq_zero` that avoids typeclass search. -/
lemma probFailure_eq_zero' [HasEvalSPMF m]
    {mx : m α} (h : NeverFail mx) : Pr[⊥ | mx] = 0 :=
  NeverFail.probFailure_eq_zero

namespace HasEvalPMF

/-- A computation in a monad with `HasEvalPMF` can't fail as outputs sum to probability `1`.  -/
instance [HasEvalPMF m] (mx : m α) : NeverFail mx where
  probFailure_eq_zero := probFailure_eq_zero mx

end HasEvalPMF

namespace HasEvalSPMF

variable [HasEvalSPMF m]

@[grind =]
lemma neverFail_iff (mx : m α) : NeverFail mx ↔ Pr[⊥ | mx] = 0 :=
  ⟨by aesop, NeverFail.mk⟩

@[simp]
instance neverFail_pure (x : α) : NeverFail (pure x : m α) := by grind

@[simp, grind =]
lemma neverFail_bind_iff (mx : m α) (my : α → m β) :
    NeverFail (mx >>= my) ↔ NeverFail mx ∧ ∀ x ∈ support mx, NeverFail (my x) := by
  simp [neverFail_iff, probFailure_bind_eq_tsum, add_eq_zero]
  grind

@[simp, grind =]
lemma neverFail_map_iff [LawfulMonad m] (mx : m α) (f : α → β) :
    NeverFail (f <$> mx) ↔ NeverFail mx := by
  grind [= map_eq_bind_pure_comp]

end HasEvalSPMF

namespace HasEvalSet

@[simp]
lemma not_neverFail_failure {m : Type u → Type v} [AlternativeMonad m]
    [HasEvalSPMF m] [HasEvalSet.LawfulFailure m] :
    ¬ NeverFail (failure : m α) := by
  simp [HasEvalSPMF.neverFail_iff]

end HasEvalSet

namespace NeverFail

variable [HasEvalSPMF m]

lemma of_probFailure_eq_zero (mx : m α) (h : Pr[⊥ | mx] = 0) : NeverFail mx :=
  { probFailure_eq_zero := h }

/--
If `mx` is a pure return, it never fails.
This follows since `evalDist (pure x)` is the Dirac distribution on `some x`.
-/
@[simp, grind .]
instance instPure {x} : NeverFail (pure x : m α) where
  probFailure_eq_zero := by simp [probFailure]

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
  probFailure_eq_zero := by
    simp [probFailure_bind_eq_tsum]
    simp [HasEvalSPMF.neverFail_iff] at hy
    tauto

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
@[simp, grind .]
instance instMap [LawfulMonad m] {mx : m α} [h : NeverFail mx] (f : α → β) :
    NeverFail (f <$> mx) := by
  simp only [map_eq_bind_pure_comp, bind_of_forall, Function.comp_def]



/-- If both the function computation and the argument computation never fail,
then their applicative sequencing also never fails. -/
@[simp, grind .]
instance instSeq [LawfulMonad m] {mf : m (α → β)} {mx : m α}
    [hf : NeverFail mf] [hx : NeverFail mx] :
    NeverFail (mf <*> mx) := by
  -- `mf <*> mx = mf >>= fun f => f <$> mx`, and mapping preserves `NeverFail` given `hx`.
  simpa [seq_eq_bind_map] using
    (bind_of_forall (mx := mf) (my := fun f => f <$> mx)
      (hx := hf) (hy := fun f => by simpa))

/-- If `mx` and `my` never fail, then `mx <* my` never fails. -/
@[simp, grind .]
instance instSeqLeft [LawfulMonad m] {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx <* my) := by
  simp [seqLeft_eq]

/-- If `mx` and `my` never fail, then `mx *> my` never fails. -/
@[simp, grind .]
instance instSeqRight [LawfulMonad m] {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx *> my) := by
  simp [seqRight_eq]


example [LawfulMonad m] (mx : m α) [h : NeverFail mx] : NeverFail (do
    let x ← mx
    let y ← mx
    return (x, y)) := by
  grind

end NeverFail
