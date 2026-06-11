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
  induction x <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure]

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
    (simulateQ impl mx >>= fun a => simulateQ impl (f a) : OptionT n β) := by
  apply simulateQ_optionT_bind'

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
    -- First step: substitute `simulateQ impl (f a) = pure (some (g a))`.
    have h₁ : (f a : OracleComp spec (Option β)) = (f a).run := rfl
    rw [← h₁, hfg a]
    simp only [Option.elimM, pure_bind, Option.elim_some]
    -- Inner bind: `let rs ← rest.mapM f; pure (b :: rs)`.
    rw [simulateQ_optionT_bind'']
    have h₂ : (rest.mapM f : OracleComp spec (Option (List β))) =
        (rest.mapM f : OptionT (OracleComp spec) (List β)).run := rfl
    rw [← h₂, ih]
    simp only [Option.elimM, pure_bind, Option.elim_some]
    change simulateQ impl ((pure (g a :: rest.map g) : OptionT (OracleComp spec) (List β)).run) = _
    exact simulateQ_pure impl (some (g a :: rest.map g))

/-- `simulateQ` over `Vector.mapM` in `OptionT`: when each step is `pure (some (g x))`
under `simulateQ`, the whole `mapM` is `pure (some (xs.map g))`. -/
lemma simulateQ_optionT_mapM_pure {k : ℕ}
    (f : α → OptionT (OracleComp spec) β) (g : α → β) (xs : Vector α k)
    (hfg : ∀ x, simulateQ impl (f x : OracleComp spec (Option β)) =
      (pure (some (g x)) : n (Option β))) :
    simulateQ impl ((xs.mapM f : OptionT (OracleComp spec) (Vector β k)) :
      OracleComp spec (Option (Vector β k))) =
    (pure (some (xs.map g)) : n (Option (Vector β k))) := by
  -- Bridge through `xs.toList`: at the `OptionT` level, `toArray <$> mapM` factors
  -- through the list version.
  have h_vl :
      (Vector.toArray <$> xs.mapM f : OptionT (OracleComp spec) (Array β)) =
        List.toArray <$> xs.toList.mapM f :=
    (Vector.toArray_mapM (xs := xs) (f := f)).trans Array.mapM_eq_mapM_toList
  -- Push to the `OracleComp` (run) level via `OptionT.run_map`.
  have h_run :
      Option.map Vector.toArray <$>
        ((xs.mapM f : OptionT (OracleComp spec) (Vector β k)) :
          OracleComp spec (Option (Vector β k))) =
      Option.map List.toArray <$>
        ((xs.toList.mapM f : OptionT (OracleComp spec) (List β)) :
          OracleComp spec (Option (List β))) := by
    have h : (Vector.toArray <$> xs.mapM f : OptionT (OracleComp spec) (Array β)).run =
        (List.toArray <$> xs.toList.mapM f : OptionT (OracleComp spec) (Array β)).run :=
      congrArg OptionT.run h_vl
    rw [OptionT.run_map, OptionT.run_map] at h
    exact h
  -- Apply `simulateQ` and push it through `<$>` using `simulateQ_map`.
  have h_sim := congrArg (simulateQ impl) h_run
  rw [simulateQ_map, simulateQ_map] at h_sim
  -- Reduce the list side via the list lemma.
  rw [simulateQ_optionT_list_mapM_pure impl f g xs.toList hfg] at h_sim
  -- Normalize the RHS so both sides have shape `Option.map Vector.toArray <$> _`.
  have h_simp_rhs :
      (Option.map List.toArray <$>
          (pure (some (xs.toList.map g)) : n (Option (List β)))) =
      Option.map Vector.toArray <$>
        (pure (some (xs.map g)) : n (Option (Vector β k))) := by
    rw [map_pure, map_pure]
    congr 1
    simp only [Option.map_some, Option.some.injEq]
    rw [← Vector.toList_map]; exact Array.toArray_toList
  rw [h_simp_rhs] at h_sim
  -- Invert `Option.map Vector.toArray <$> _` via injectivity.
  have h_inj : ∀ {x y : Option (Vector β k)},
      Option.map Vector.toArray x = Option.map Vector.toArray y → x = y := by
    intro x y hxy
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hxy
    · rfl
    · exact congrArg some (Vector.toArray_inj.mp hxy)
  exact (map_inj_right h_inj).mp h_sim

/-! ## `forIn` over `OptionT`

The `List` companions to `simulateQ_optionT_bind`/`_lift` for an `OptionT`-monadic loop. -/

/-- `simulateQ` distributes over an `OptionT`-monadic `forIn` on a list: the `OptionT`-loop
sibling of `simulateQ_list_forIn`. The body lives in `OptionT (OracleComp spec)`, so the loop is
decomposed via `simulateQ_optionT_bind` (rather than the `OracleComp`-level `simulateQ_bind` that
`simulateQ_list_forIn` uses). Needed to push `simulateQ` past a verifier's spot-check
`for j in List.finRange t do …` when that loop is `OptionT`-monadic. -/
lemma simulateQ_optionT_list_forIn (xs : List α) (init : β)
    (body : α → β → OptionT (OracleComp spec) (ForInStep β)) :
    simulateQ impl ((forIn xs init body : OptionT (OracleComp spec) β) :
        OracleComp spec (Option β))
      = ((forIn xs init (fun a b => simulateQ impl (body a b)) : OptionT n β) :
        n (Option β)) := by
  induction xs generalizing init with
  | nil =>
      rw [List.forIn_nil, List.forIn_nil]
      exact simulateQ_pure impl (some init)
  | cons x rest ih =>
      rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind]
      refine bind_congr fun step => ?_
      cases step with
      | done b =>
          change simulateQ impl ((pure b : OptionT (OracleComp spec) β) :
            OracleComp spec (Option β)) = _
          exact simulateQ_pure impl (some b)
      | yield b => exact ih b

/-- If under `simulateQ` every loop body resolves to `pure (some (ForInStep.yield init))` (yields
the accumulator unchanged at the initial value), the whole `OptionT`-monadic `forIn` resolves to
`pure (some init)`. Discharges a verifier spot-check loop whose body is a sequence of oracle reads
followed by an always-passing `guard` (under the relevant accept hypothesis). The constant-yield
`OptionT` companion to `simulateQ_list_forIn`. -/
lemma simulateQ_optionT_forIn_yield_pure_some (xs : List α) (init : β)
    (body : α → β → OptionT (OracleComp spec) (ForInStep β))
    (hbody : ∀ a, simulateQ impl ((body a init : OptionT (OracleComp spec) (ForInStep β)) :
        OracleComp spec (Option (ForInStep β)))
      = (pure (some (ForInStep.yield init)) : n (Option (ForInStep β)))) :
    simulateQ impl ((forIn xs init body : OptionT (OracleComp spec) β) :
        OracleComp spec (Option β))
      = (pure (some init) : n (Option β)) := by
  rw [simulateQ_optionT_list_forIn]
  induction xs with
  | nil => rw [List.forIn_nil]; rfl
  | cons x rest ih =>
      rw [List.forIn_cons]
      change ((simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
          OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β)) >>= _ :
          OptionT n β) = _
      rw [show (simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
          OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β))
          = (pure (ForInStep.yield init) : OptionT n (ForInStep β)) from hbody x]
      rw [pure_bind]
      exact ih

-- section OptionT

-- omit [LawfulMonad n] in
-- @[simp] lemma simulateQ_option_elim (x : Option α) (my : OracleComp spec β)
--     (my' : α → OracleComp spec β) : simulateQ impl (x.elim my my') =
--     x.elim (simulateQ impl my) (fun x => simulateQ impl (my' x)) := by
--   cases x <;> simp

-- @[simp] lemma simulateQ_option_elimM (mx : OracleComp spec (Option α))
--     (my : OracleComp spec β) (my' : α → OracleComp spec β) :
--     simulateQ impl (Option.elimM mx my my') =
--     Option.elimM (simulateQ impl mx) (simulateQ impl my) (fun x => simulateQ impl (my' x)) := by
--   unfold Option.elimM
--   rw [simulateQ_bind]
--   exact bind_congr fun x => simulateQ_option_elim impl x my my'

-- /-- `simulateQ` distributes through `OptionT.bind`, stated via `OptionT.run`. -/
-- lemma simulateQ_optionT_bind'
--     (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
--     simulateQ impl (mx >>= f).run =
--     (simulateQ impl mx.run >>= fun a => simulateQ impl (f a).run : OptionT n β) := by
--   rw [OptionT.run_bind, Option.elimM, simulateQ_bind]
--   refine bind_congr fun x => ?_
--   induction x <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure]

-- /-- `simulateQ` distributes through `OptionT.bind`, stated via `Option.elimM`. -/
-- lemma simulateQ_optionT_bind''
--     (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
--     simulateQ impl (mx >>= f).run =
--     Option.elimM (simulateQ impl mx.run) (pure none) (fun a => simulateQ impl (f a).run) := by
--   simp

-- /-- `simulateQ` distributes through `OptionT.bind`: the simulated OptionT-bind is the
--     OptionT-bind of the simulated pieces. -/
-- lemma simulateQ_optionT_bind
--     (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
--     simulateQ impl (mx >>= f : OptionT (OracleComp spec) β) =
--     (simulateQ impl mx >>= fun a => simulateQ impl (f a) : OptionT n β) := by
--   apply simulateQ_optionT_bind'

-- /-- `simulateQ` commutes with `OptionT.lift`. -/
-- @[simp] lemma simulateQ_optionT_lift
--     (comp : OracleComp spec α) :
--     simulateQ impl (OptionT.lift comp : OptionT (OracleComp spec) α) =
--       (OptionT.lift (simulateQ impl comp) : OptionT n α) := by
--   simp only [OptionT.lift, OptionT.mk, simulateQ_bind, simulateQ_pure]

-- end OptionT
