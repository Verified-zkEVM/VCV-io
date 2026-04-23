/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.IdenticalUntilBad
import VCVio.HeapSSP.Composition

/-!
# Mini Fiat-Shamir pilot on HeapSSP

Pilot exercise validating the "monolithic real vs link-composite sim"
H3 pattern used in the Fiat-Shamir CMA → NMA restructure
(see `~/Documents/Notes/vcvio-fs-ssp-heapssp-restructure.md`), on a
minimal setup carrying:

* **outer cells**: a single `counter : ℕ`, holding the number of issued
  export queries;
* **inner cells**: a single `bad : Bool` flag, flipped whenever the inner
  RO sampler produces `true`.

The pilot asserts three things in order of importance:

1. **Type-level alignment.** `simGame := outer.link inner` and `realGame`
   are both `Package unifSpec exportSpec (OuterCell ⊕ BadCell)`; no
   bijection required between their state spaces.
2. **Bridge applicability.** The heap identical-until-bad bridge
   (`Package.advantage_le_qSeps_plus_probEvent_bad` in
   `VCVio/HeapSSP/IdenticalUntilBad.lean`) applies directly: all hypotheses
   (initial heap, per-step equality below `bad = false`, monotonicity above
   it) discharge cleanly, yielding
   `advantage ≤ qS · ε + Pr[bad | realGame.run A]`.
3. **ε = 0 collapse.** Because `realGame.impl` is definitionally the
   same expression as `simGame.impl` in the `bad = false` branch (the two
   share a common `linkReshape <$> ...` body), the per-step TV distance
   is `0`, and the bridge collapses to
   `advantage ≤ Pr[bad | realGame.run A]`.

Numeric bounds on `Pr[bad | ...]` (e.g., `qS / 2` for uniform Boolean
sampling) are deferred to the real FS cutover; the pilot's mandate is to
validate that the bridge *applies* with the intended shape.

## What the pilot does **not** validate

The pilot is deliberately minimal: both games share the same
`linkReshape <$> ...` body whenever `bad = false`, so the per-step
equality is *definitional* rather than distributional. In the real FS
cutover, the per-step equality has real probabilistic content (the
programming RO and the uniform RO agree as distributions, not as terms),
so the `h_step_tv_S` hypothesis is discharged by an `evalDist`-level
argument rather than by `rfl`. -/

open OracleSpec OracleComp ENNReal ProbComp

namespace VCVio.HeapSSP.MiniFS

open VCVio.HeapSSP.Package

/-! ## Oracle specs -/

/-- Inner oracle-spec index: a single query `rand` returning a random
`Bool`. -/
inductive InnerOp
  | rand
  deriving DecidableEq

/-- Inner import interface: `rand` samples a `Bool`. -/
@[reducible] def innerSpec : OracleSpec.{0, 0} InnerOp
  | .rand => Bool

/-- Export oracle-spec index: a single export query `op`. -/
inductive ExportOp
  | op
  deriving DecidableEq

/-- Export interface: `op` returns a `Bool`. -/
@[reducible] def exportSpec : OracleSpec.{0, 0} ExportOp
  | .op => Bool

/-! ## Cell directories

Both the link-composite `simGame` and the monolithic `realGame` share the
identifier set `OuterCell ⊕ BadCell`. -/

/-- Outer cell directory: one counter cell. -/
inductive OuterCell
  | counter
  deriving DecidableEq

instance : CellSpec OuterCell where
  type    | .counter => ℕ
  default | .counter => 0

/-- Inner cell directory: one bad flag cell. -/
inductive BadCell
  | bad
  deriving DecidableEq

instance : CellSpec BadCell where
  type    | .bad => Bool
  default | .bad => false

/-- The composite cell directory shared by `simGame` and `realGame`. -/
abbrev MiniCells := OuterCell ⊕ BadCell

/-! ## Packages -/

/-- The inner package, owning the `bad` flag.

On `.rand`, it samples a uniform `Bool` and writes it to `.bad`; if `.bad`
is already set, it short-circuits to `pure (false, h)` without sampling.
The short-circuit makes `bad`-monotonicity definitional on the inner side. -/
def inner : Package unifSpec innerSpec BadCell where
  init := pure Heap.empty
  impl
    | .rand => StateT.mk fun h =>
        if h .bad then
          pure (false, h)
        else do
          let b ← ($ᵗ Bool)
          pure (b, h.update .bad b)

/-- The outer package, owning the `counter`.

On `.op`, it imports one `.rand` from the inner spec, increments the
counter, and returns the sampled bit unchanged. -/
def outer : Package innerSpec exportSpec OuterCell where
  init := pure Heap.empty
  impl
    | .op => StateT.mk fun h => do
        let b ← (innerSpec.query .rand : OracleComp innerSpec Bool)
        pure (b, h.update .counter (h.get .counter + 1))

/-- The **simulated game** : `outer.link inner`, with composite state
`Heap MiniCells = Heap (OuterCell ⊕ BadCell)`. -/
def simGame : Package unifSpec exportSpec MiniCells :=
  outer.link inner

/-- The **real game** : monolithic package over the *same* `MiniCells`.

The `bad = false` branch is defined to be the same expression as the
body of `simGame.impl`, i.e., `linkReshape <$> (simulateQ inner.impl
...).run ...`. This makes per-step equality below the bad line hold by
`rfl`. The `bad = true` branch short-circuits to `pure (true, h)`,
which is *different* from `simGame`'s behaviour (both are correct under
identical-until-bad reasoning — the bridge never compares them past
`bad`). -/
def realGame : Package unifSpec exportSpec MiniCells where
  init := pure Heap.empty
  impl
    | .op => StateT.mk fun h =>
        if h (.inr .bad) then
          pure (true, h)
        else
          linkReshape <$>
            (simulateQ inner.impl
              ((outer.impl .op).run (Heap.split _ _ h).1)).run
              (Heap.split _ _ h).2

/-! ## Target 1 — Type-level structural match -/

/-- **`simGame` and `realGame` live over the same state type**, by
construction: both are `Package unifSpec exportSpec MiniCells`. This is
the "H4 is `rfl`" plank of the design: no bijection is needed between
the two games' states. -/
example : Package unifSpec exportSpec MiniCells := simGame
example : Package unifSpec exportSpec MiniCells := realGame

/-- Both packages initialise to `pure Heap.empty`. -/
example : realGame.init = (pure Heap.empty : ProbComp (Heap MiniCells)) := rfl

/-! ## Bijection extracting the bad flag

`σ := Heap OuterCell`: the "state below the bad line" is the outer half of
the heap. The bijection `φ` reads off the bad cell and returns the outer
half together with its value. -/

/-- The bridge bijection: split the heap, read the `bad` cell. -/
def φ : Heap MiniCells ≃ Heap OuterCell × Bool where
  toFun h := ((Heap.split _ _ h).1, h (.inr .bad))
  invFun p := fun i =>
    match i with
    | .inl a => p.1 a
    | .inr .bad => p.2
  left_inv h := by
    funext i
    rcases i with a | c
    · rfl
    · cases c
      rfl
  right_inv := fun ⟨_, _⟩ => rfl

@[simp] lemma φ_snd_apply (h : Heap MiniCells) : (φ h).2 = h (.inr .bad) := rfl

@[simp] lemma φ_symm_apply_inl (h_out : Heap OuterCell) (b : Bool) (a : OuterCell) :
    (φ.symm (h_out, b) : Heap MiniCells) (.inl a) = h_out a := rfl

@[simp] lemma φ_symm_apply_inr (h_out : Heap OuterCell) (b : Bool) :
    (φ.symm (h_out, b) : Heap MiniCells) (.inr .bad) = b := rfl

/-- `φ.symm (Heap.empty, false) = Heap.empty`. -/
lemma φ_symm_empty_false :
    φ.symm ((Heap.empty : Heap OuterCell), false) = (Heap.empty : Heap MiniCells) := by
  funext i
  rcases i with a | c
  · rfl
  · cases c
    rfl

/-! ## Bridge hypotheses, factored out for readability -/

/-- `simGame.init` reduces to `pure Heap.empty`. -/
lemma simGame_init_eq : simGame.init = (pure Heap.empty : ProbComp (Heap MiniCells)) := by
  change (outer.link inner).init = _
  rw [link_init]
  rfl

/-- **Per-step agreement below the bad line.** When `bad = false`, the
`.op`-handler of `realGame` is definitionally the same as that of
`simGame`: both evaluate to the shared `linkReshape <$> ...` body. -/
lemma realGame_impl_op_eq_simGame_impl_op
    (s : Heap OuterCell) :
    (realGame.impl .op).run (φ.symm (s, false))
      = (simGame.impl .op).run (φ.symm (s, false)) := rfl

/-! ## Target 2 — Apply the heap identical-until-bad bridge

With `S := fun _ => True` (the one export query `.op` is always "costly"),
`ε := 0`, and `φ` the bijection above, the bridge produces:

```
ENNReal.ofReal (realGame.advantage simGame A) ≤ qS · 0 + Pr[bad | realGame.run A]
                                              = Pr[bad | realGame.run A]
```

for every `A : OracleComp exportSpec Bool` with at most `qS` queries. -/

/-- **Heap identical-until-bad bridge, applied.**

The advantage of any Boolean adversary `A` against `realGame` vs. `simGame`
is bounded by the probability that `bad = true` holds at the end of
`realGame`'s run against `A`. -/
theorem realGame_advantage_le_probEvent_bad
    {qS : ℕ}
    (A : OracleComp exportSpec Bool)
    (h_qb : OracleComp.IsQueryBound A qS
      (fun _ b => 0 < b)
      (fun _ b => b - 1)) :
    ENNReal.ofReal (realGame.advantage simGame A)
      ≤ Pr[fun z : Bool × Heap MiniCells => (φ z.2).2 = true |
          (simulateQ realGame.impl A).run (φ.symm (Heap.empty, false))] := by
  have h_qb' : OracleComp.IsQueryBound A qS
      (fun t b => if (fun _ => True) t then 0 < b else True)
      (fun t b => if (fun _ => True) t then b - 1 else b) := by
    simpa using h_qb
  have h :=
    Package.advantage_le_qSeps_plus_probEvent_bad
      (G₀ := realGame) (G₁ := simGame)
      (φ := φ) (s_init := (Heap.empty : Heap OuterCell))
      (h_init₀ := by
        show realGame.init = pure (φ.symm ((Heap.empty : Heap OuterCell), false))
        rw [φ_symm_empty_false]
        rfl)
      (h_init₁ := by
        rw [simGame_init_eq, φ_symm_empty_false])
      (S := fun _ => True) (ε := 0)
      (h_step_tv_S := by
        intro t _ s
        cases t
        rw [realGame_impl_op_eq_simGame_impl_op s, tvDist_self]
        simp)
      (h_step_eq_nS := fun _ ht _ => absurd trivial ht)
      (h_mono₀ := by
        intro t h hbad z hz
        cases t
        have h_bad_true : h (.inr .bad) = true := by simpa using hbad
        -- Reduce `realGame.impl .op . run h` via the if-branch.
        change z ∈ support
          (if h (.inr .bad) then
             (pure (true, h) : OracleComp unifSpec (Bool × Heap MiniCells))
           else
             linkReshape <$>
               (simulateQ inner.impl
                 ((outer.impl .op).run (Heap.split _ _ h).1)).run
                 (Heap.split _ _ h).2) at hz
        rw [if_pos h_bad_true] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        simpa using hbad)
      A h_qb'
  simpa using h

/-! ## Target 3 — Single-query adversary and concrete bound

A concrete instance: the one-query adversary `encOnce := exportSpec.query .op`
(which returns the bit directly, reinterpreted as the adversary's Boolean
guess) bounds the advantage by the probability that the single sampled bit
lands on `true`. -/

/-- The canonical one-query adversary: issue `.op` once and return the
result. -/
def oneQueryAdversary : OracleComp exportSpec Bool := exportSpec.query .op

/-- `oneQueryAdversary` is `IsQueryBound` at `qS = 1` under the
"each query decrements the budget" cost model. -/
lemma oneQueryAdversary_isQueryBound :
    OracleComp.IsQueryBound oneQueryAdversary 1
      (fun _ b => 0 < b) (fun _ b => b - 1) := by
  unfold oneQueryAdversary
  simp

/-- **Headline bound for the one-query adversary.** Against
`oneQueryAdversary`, the advantage of `realGame` vs. `simGame` is bounded
by the probability that `realGame`'s single sampled bit hits `true`, which
collapses to the bad-event probability on the pilot's shape. -/
theorem oneQueryAdversary_advantage_le_probEvent_bad :
    ENNReal.ofReal (realGame.advantage simGame oneQueryAdversary)
      ≤ Pr[fun z : Bool × Heap MiniCells => (φ z.2).2 = true |
          (simulateQ realGame.impl oneQueryAdversary).run
            (φ.symm (Heap.empty, false))] :=
  realGame_advantage_le_probEvent_bad (qS := 1) oneQueryAdversary
    oneQueryAdversary_isQueryBound

end VCVio.HeapSSP.MiniFS
