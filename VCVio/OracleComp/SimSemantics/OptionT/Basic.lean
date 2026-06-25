/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.SimulateQ
import ToMathlib.Control.OptionT

/-!
# Simulation Semantics through `OptionT` Handlers

Distributivity lemmas for `simulateQ` over `OptionT`-shaped operations
(`Option.elim`, `Option.elimM`, `OptionT.bind`, `OptionT.lift`).

These lemmas appeal to the central `simulateQ` theory in
`VCVio.OracleComp.SimSemantics.SimulateQ`; the file is grouped under
`SimSemantics/OptionT/` to mirror the per-transformer organization used for
`StateT`, `WriterT`, and `ReaderT`.
-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u}

variable {ι} {spec : OracleSpec ι} {r n : Type u → Type*}
    [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

omit [LawfulMonad n] in
@[simp] lemma simulateQ_option_elim (x : Option α) (my : OracleComp spec β)
    (my' : α → OracleComp spec β) : simulateQ impl (x.elim my my') =
    x.elim (simulateQ impl my) (fun x => simulateQ impl (my' x)) := by
  cases x <;> simp

@[simp] lemma simulateQ_option_elimM (mx : OracleComp spec (Option α))
    (my : OracleComp spec β) (my' : α → OracleComp spec β) :
    simulateQ impl (Option.elimM mx my my') =
    Option.elimM (simulateQ impl mx) (simulateQ impl my) (fun x => simulateQ impl (my' x)) := by
  unfold Option.elimM
  rw [simulateQ_bind]
  exact bind_congr fun x => simulateQ_option_elim impl x my my'

/-- `simulateQ` distributes through `OptionT.bind`, stated via `OptionT.run`. -/
lemma simulateQ_optionT_bind'
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    simulateQ impl (mx >>= f).run =
    (simulateQ impl mx.run >>= fun a => simulateQ impl (f a).run : OptionT n β) := by
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind]
  refine bind_congr fun x => ?_
  induction x <;> simp

/-- `simulateQ` distributes through `OptionT.bind`, stated via `Option.elimM`. -/
lemma simulateQ_optionT_bind''
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    simulateQ impl (mx >>= f).run =
    Option.elimM (simulateQ impl mx.run) (pure none) (fun a => simulateQ impl (f a).run) := by
  simp

/-- `simulateQ` distributes through `OptionT.bind`: the simulated OptionT-bind is the
    OptionT-bind of the simulated pieces. -/
lemma simulateQ_optionT_bind
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    simulateQ impl (mx >>= f : OptionT (OracleComp spec) β) =
    (simulateQ impl mx >>= fun a => simulateQ impl (f a) : OptionT n β) :=
  simulateQ_optionT_bind' impl mx f

/-- `simulateQ` commutes with `OptionT.lift`. -/
@[simp] lemma simulateQ_optionT_lift
    (comp : OracleComp spec α) :
    simulateQ impl (OptionT.lift comp : OptionT (OracleComp spec) α) =
      (OptionT.lift (simulateQ impl comp) : OptionT n α) := by
  simp only [OptionT.lift, OptionT.mk, simulateQ_bind, simulateQ_pure]

/-! ## `mapM` over `OptionT`

When every step of a `mapM` resolves to `pure (some _)` under `simulateQ`,
the whole `mapM` resolves to `pure (some _)` of the pointwise mapped collection.
These are the `List` and `Vector` companions to `simulateQ_optionT_bind'` /
`simulateQ_optionT_lift`. -/

/-- `simulateQ` over `List.mapM` in `OptionT`: when each step is `pure (some (g x))`
under `simulateQ`, the whole `mapM` is `pure (some (l.map g))`. -/
lemma simulateQ_optionT_list_mapM_pure
    (f : α → OptionT (OracleComp spec) β) (g : α → β) (l : List α)
    (hfg : ∀ x, simulateQ impl (f x : OracleComp spec (Option β)) =
      (pure (some (g x)) : n (Option β))) :
    simulateQ impl ((l.mapM f : OptionT (OracleComp spec) (List β)) :
      OracleComp spec (Option (List β))) =
    (pure (some (l.map g)) : n (Option (List β))) := by
  induction l with
  | nil => exact simulateQ_pure impl (some [])
  | cons a rest ih =>
    change simulateQ impl ((a :: rest).mapM f : OptionT (OracleComp spec) (List β)).run = _
    rw [List.mapM_cons, simulateQ_optionT_bind'']
    have h₁ : (f a : OracleComp spec (Option β)) = (f a).run := rfl
    rw [← h₁, hfg a]
    simp only [Option.elimM, pure_bind, Option.elim_some]
    rw [simulateQ_optionT_bind'']
    have h₂ : (rest.mapM f : OracleComp spec (Option (List β))) =
        (rest.mapM f : OptionT (OracleComp spec) (List β)).run := rfl
    rw [← h₂, ih]
    simp only [Option.elimM, pure_bind, Option.elim_some, OptionT.run_pure, simulateQ_pure,
      List.map_cons]

/-- `simulateQ` over `Vector.mapM` in `OptionT`: when each step is `pure (some (g x))`
under `simulateQ`, the whole `mapM` is `pure (some (xs.map g))`. -/
lemma simulateQ_optionT_mapM_pure {k : ℕ}
    (f : α → OptionT (OracleComp spec) β) (g : α → β) (xs : Vector α k)
    (hfg : ∀ x, simulateQ impl (f x : OracleComp spec (Option β)) =
      (pure (some (g x)) : n (Option β))) :
    simulateQ impl ((xs.mapM f : OptionT (OracleComp spec) (Vector β k)) :
      OracleComp spec (Option (Vector β k))) =
    (pure (some (xs.map g)) : n (Option (Vector β k))) := by
  have h_vl :
      (Vector.toArray <$> xs.mapM f : OptionT (OracleComp spec) (Array β)) =
        List.toArray <$> xs.toList.mapM f :=
    (Vector.toArray_mapM (xs := xs) (f := f)).trans Array.mapM_eq_mapM_toList
  have h_run :
      Option.map Vector.toArray <$>
        ((xs.mapM f : OptionT (OracleComp spec) (Vector β k)) :
          OracleComp spec (Option (Vector β k))) =
      Option.map List.toArray <$>
        ((xs.toList.mapM f : OptionT (OracleComp spec) (List β)) :
          OracleComp spec (Option (List β))) := by
    simpa only [OptionT.run_map] using congrArg OptionT.run h_vl
  have h_sim := congrArg (simulateQ impl) h_run
  rw [simulateQ_map, simulateQ_map, simulateQ_optionT_list_mapM_pure impl f g xs.toList hfg]
    at h_sim
  have h_simp_rhs :
      (Option.map List.toArray <$>
          (pure (some (xs.toList.map g)) : n (Option (List β)))) =
      Option.map Vector.toArray <$>
        (pure (some (xs.map g)) : n (Option (Vector β k))) := by
    simp only [map_pure, Option.map_some, ← Vector.toList_map, Vector.toArray_toList]
  rw [h_simp_rhs] at h_sim
  exact (map_inj_right
    (fun h => Option.map_injective (fun _ _ => Vector.toArray_inj.mp) h)).mp h_sim
