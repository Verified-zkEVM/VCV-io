/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Generic-monad probability tactic benchmark

A companion to `VCVioTest/ProbabilityTactics.lean`. That file gates `simp`/`grind` over concrete
`ProbComp`; this one gates them over a **generic monad `m`** with the EvalDist instance stack
(`[MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
[EvalDistCompatible m]`), where the probability / support / distribution lemmas are actually stated,
plus over the concrete transformer instances (`OptionT`, `ExceptT`, `ReaderT`, `SPMF`, `Id`).

Testing generically exercises facts `ProbComp` masks. The headline is the **failure
factor**: over a failing monad, `Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my]`, while
`Pr[⊥ | mx *> my]` is inclusion–exclusion `Pr[⊥|mx] + Pr[⊥|my] - Pr[⊥|mx]*Pr[⊥|my]`; both collapse
only when `Pr[⊥] = 0` (as in `ProbComp`).

As in the concrete battery: where a fact closes by both `simp` and `grind`, both are kept (the
mirror); otherwise a single terminal tactic + a `target(...)` note. Operations with no probability
API yet are recorded as `target` gaps at the end.
-/

open OracleComp ProbComp ENNReal

namespace VCVioTest.MonadProbability

/-! # Generic monad `m` -/

section generic

variable {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

/-! ## `pure` — all heads close by both `simp` and `grind`. -/

example (x : α) : Pr[= x | (pure x : m α)] = 1 := by simp
example (x : α) : Pr[= x | (pure x : m α)] = 1 := by grind

example (p : α → Prop) [DecidablePred p] (x : α) :
    Pr[ p | (pure x : m α)] = if p x then 1 else 0 := by simp
example (p : α → Prop) [DecidablePred p] (x : α) :
    Pr[ p | (pure x : m α)] = if p x then 1 else 0 := by grind

example (x : α) : Pr[⊥ | (pure x : m α)] = 0 := by simp
example (x : α) : Pr[⊥ | (pure x : m α)] = 0 := by grind

example (x : α) : support (pure x : m α) = {x} := by simp
example (x : α) : support (pure x : m α) = {x} := by grind

example (x : α) : 𝒟[(pure x : m α)] = pure x := by simp
example (x : α) : 𝒟[(pure x : m α)] = pure x := by grind

/-! ## `bind`

The support is a union; the distribution is a `bind`; the outcome/event/failure probabilities are
`tsum`s (`grind`-only — they are `@[grind =]`, not `@[simp]`). -/

example (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by simp
example (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by grind

example (mx : m α) (my : α → m β) : 𝒟[mx >>= my] = 𝒟[mx] >>= fun x => 𝒟[my x] := by simp
example (mx : m α) (my : α → m β) : 𝒟[mx >>= my] = 𝒟[mx] >>= fun x => 𝒟[my x] := by grind

-- target(simp): the `tsum` bind expansions are `@[grind =]` only.
example (mx : m α) (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by grind
example (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by grind

/-! ## `bind` with a constant continuation — the failure factor

`Pr[= y | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[= y | my]`: the factor `(1 - Pr[⊥ | mx])` is
the probability `mx` succeeds at all. -/

example (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by simp
example (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by grind

example (mx : m α) (my : m β) :
    Pr[⊥ | mx >>= fun _ => my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by simp
example (mx : m α) (my : m β) :
    Pr[⊥ | mx >>= fun _ => my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by grind

/-! ## `map` (`<$>`)

`probFailure`/`probEvent` are invariant / pulled back; `support` is the image; the new
`probOutput_map` is the `grind`-only pulled-back outcome. -/

example (f : α → β) (mx : m α) : Pr[⊥ | f <$> mx] = Pr[⊥ | mx] := by simp
example (f : α → β) (mx : m α) : Pr[⊥ | f <$> mx] = Pr[⊥ | mx] := by grind

example (f : α → β) (mx : m α) (q : β → Prop) : Pr[ q | f <$> mx] = Pr[ q ∘ f | mx] := by simp
example (f : α → β) (mx : m α) (q : β → Prop) : Pr[ q | f <$> mx] = Pr[ q ∘ f | mx] := by grind

example (f : α → β) (mx : m α) : support (f <$> mx) = f '' support mx := by simp
example (f : α → β) (mx : m α) : support (f <$> mx) = f '' support mx := by grind

example (f : α → β) (mx : m α) : 𝒟[f <$> mx] = f <$> 𝒟[mx] := by simp
example (f : α → β) (mx : m α) : 𝒟[f <$> mx] = f <$> 𝒟[mx] := by grind

-- target(simp): `probOutput_map` is `@[grind =]` only (`simp` keeps its injective/equiv map forms).
example (f : α → β) (mx : m α) (y : β) :
    Pr[= y | f <$> mx] = Pr[ fun x => f x = y | mx] := by grind

/-! ## `seqLeft` (`<*`) / `seqRight` (`*>`) — the headline failure factors

The discarded computation contributes only its *success* mass `(1 - Pr[⊥])`; the combined failure is
inclusion–exclusion. Over `ProbComp` (`Pr[⊥] = 0`) these collapse to `Pr[= _ | _]` and `0`. -/

example (mx my : m α) (x : α) : Pr[= x | mx <* my] = (1 - Pr[⊥ | my]) * Pr[= x | mx] := by simp
example (mx my : m α) (x : α) : Pr[= x | mx <* my] = (1 - Pr[⊥ | my]) * Pr[= x | mx] := by grind

example (mx my : m α) (y : α) : Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by simp
example (mx my : m α) (y : α) : Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by grind

example (mx my : m α) (p : α → Prop) :
    Pr[ p | mx <* my] = (1 - Pr[⊥ | my]) * Pr[ p | mx] := by simp
example (mx my : m α) (p : α → Prop) :
    Pr[ p | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[ p | my] := by simp

example (mx my : m α) :
    Pr[⊥ | mx <* my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by simp
example (mx my : m α) :
    Pr[⊥ | mx *> my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by simp

example (mx my : m α) : 𝒟[mx *> my] = 𝒟[mx] *> 𝒟[my] := by simp
example (mx my : m α) : 𝒟[mx <* my] = 𝒟[mx] <* 𝒟[my] := by simp

/-! ## `seq` (`<*>`)

Failure is inclusion–exclusion; the `Prod.mk` product factors (`simp`-only — `grind` cannot
factor an applicative product). -/

example (mf : m (α → β)) (mx : m α) :
    Pr[⊥ | mf <*> mx] = Pr[⊥ | mf] + Pr[⊥ | mx] - Pr[⊥ | mf] * Pr[⊥ | mx] := by simp
example (mf : m (α → β)) (mx : m α) :
    Pr[⊥ | mf <*> mx] = Pr[⊥ | mf] + Pr[⊥ | mx] - Pr[⊥ | mf] * Pr[⊥ | mx] := by grind

example (mf : m (α → β)) (mx : m α) : 𝒟[mf <*> mx] = 𝒟[mf] <*> 𝒟[mx] := by simp

-- target(grind): the applicative product's second factor sits under a binder, unindexable by grind.
example (mx my : m α) (z : α × α) :
    Pr[= z | Prod.mk <$> mx <*> my] = Pr[= z.1 | mx] * Pr[= z.2 | my] := by simp

end generic

/-! # Concrete transformer instantiations

The generic lemmas specialise to each monad transformer that instantiates the framework. For
never-failing carriers (`Id`, `OptionT ProbComp`'s base) the failure factor collapses; for genuinely
failing ones it does not — that contrast is the point. -/

/-! ## `Id` -/
example (x : Bool) : Pr[= x | (pure x : Id Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (pure x : Id Bool)] = 1 := by grind
example (mx my : Id Bool) (y : Bool) : Pr[= y | mx *> my] = Pr[= y | my] := by simp

/-! ## `OptionT ProbComp` (the failing case used in cryptography) -/
example (x : Bool) : Pr[= x | (pure x : OptionT ProbComp Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (pure x : OptionT ProbComp Bool)] = 1 := by grind
example : Pr[⊥ | (failure : OptionT ProbComp Bool)] = 1 := by simp
example : Pr[⊥ | (failure : OptionT ProbComp Bool)] = 1 := by grind

-- the failure factor is visible here (the discarded draw can fail):
example (mx my : OptionT ProbComp Bool) (y : Bool) :
    Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by simp

/-! ## `ExceptT` over `ProbComp` (a failing carrier — failure factor visible) -/
example (x : Bool) : Pr[= x | (pure x : ExceptT String ProbComp Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (pure x : ExceptT String ProbComp Bool)] = 1 := by grind

/-! ## `SPMF` itself -/
example (x : Bool) : Pr[= x | (pure x : SPMF Bool)] = 1 := by simp
example (x : Bool) : Pr[= x | (pure x : SPMF Bool)] = 1 := by grind

/-! ## `orElse` (`<|>`) and `guard` over `OptionT ProbComp`

The freshly-added API (`probFailure_orElse` / `probOutput_orElse` / `support_guard`). -/

example (oa oa' : OptionT ProbComp Bool) :
    Pr[⊥ | oa <|> oa'] = Pr[⊥ | oa] * Pr[⊥ | oa'] := by simp

example (oa oa' : OptionT ProbComp Bool) (x : Bool) :
    Pr[= x | oa <|> oa'] = Pr[= x | oa] + Pr[⊥ | oa] * Pr[= x | oa'] := by simp

example (p : Prop) [Decidable p] :
    support (guard p : OptionT ProbComp Unit) = if p then {()} else ∅ := by simp

example (p : Prop) [Decidable p] :
    Pr[⊥ | (guard p : OptionT ProbComp Unit)] = if p then 0 else 1 := by simp

/-! # Remaining API gaps (`target`)

These common monad operations have no probability lemmas yet; each is a future API addition:

* `support_orElse` — `support (oa <|> oa') = support oa ∪ {x | Pr[⊥ | oa] ≠ 0 ∧ x ∈ support oa'}`;
  follows from `probOutput_orElse` via the support↔probability bridge.
* `finSupport_guard` / `probEvent_guard` / `evalDist_guard` — blocked on the
  `LawfulFailure (OptionT (OracleComp spec))` universe quirk (see `OracleComp/EvalDist.lean`).
* `forM` / `sequence` / `traverse` / `List.foldlM` — no generic probability lemmas (only `mapM` is
  covered, via `probFailure_list_mapM` / `probOutput_list_mapM`).
-/

end VCVioTest.MonadProbability
