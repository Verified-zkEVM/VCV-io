/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.HasQuery

/-!
# Random-Oracle Simulation Helpers

Generic lemmas for simulating `OracleComp (unifSpec + hashSpec)` computations via
`unifFwdImpl + ro` in `StateT hashSpec.QueryCache ProbComp`, where `unifFwdImpl` forwards
uniform-randomness queries and `ro` handles the hash oracle (typically `randomOracle`).

These lemmas factor out boilerplate shared by `FiatShamir.perfectlyCorrect`,
`FiatShamirWithAbort.correct`, and other random-oracle-model proofs.

The typical usage pattern is:

```
let ro : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp) := randomOracle
let impl := unifFwdImpl hashSpec + ro
```

Then the `roSim` namespace lemmas apply to `simulateQ impl`.

## Main definitions

* `unifFwdImpl`: the identity forwarding implementation for `unifSpec`, lifted to `StateT`
-/

open OracleComp OracleSpec

variable {ι : Type} {hashSpec : OracleSpec ι}

/-- The identity forwarding implementation for `unifSpec` queries, lifted to
`StateT hashSpec.QueryCache ProbComp`. Each uniform query passes through to the underlying
`ProbComp` without touching the cache state. -/
noncomputable def unifFwdImpl (hashSpec : OracleSpec ι) :
    QueryImpl unifSpec (StateT hashSpec.QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT hashSpec.QueryCache ProbComp)

namespace unifFwdImpl

lemma simulateQ_run {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec) oa).run s = (fun x => (x, s)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [unifFwdImpl, ← ih]

end unifFwdImpl

namespace roSim

variable (ro : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))

lemma simulateQ_liftComp {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (OracleComp.liftComp oa (unifSpec + hashSpec)) =
    simulateQ (unifFwdImpl hashSpec) oa :=
  QueryImpl.simulateQ_add_liftComp_left
    (m' := StateT hashSpec.QueryCache ProbComp)
    (unifFwdImpl hashSpec) ro oa

lemma run_liftM {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s =
      (fun x => (x, s)) <$> oa := by
  rw [show simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) =
      simulateQ (unifFwdImpl hashSpec) oa from simulateQ_liftComp ro oa]
  exact unifFwdImpl.simulateQ_run oa s

lemma run_liftM_support {α : Type} (oa : ProbComp α) (s : hashSpec.QueryCache) :
    support ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa)).run s) =
      (fun x => (x, s)) '' support oa := by
  rw [run_liftM, support_map]

lemma run'_liftM_bind {α β : Type} (oa : ProbComp α)
    (rest : α → StateT hashSpec.QueryCache ProbComp β)
    (s : hashSpec.QueryCache) :
    (simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run' s =
      oa >>= fun x => (rest x).run' s := by
  change Prod.fst <$>
    ((simulateQ (unifFwdImpl hashSpec + ro) (liftM oa) >>= rest).run s) =
    oa >>= fun x => Prod.fst <$> (rest x).run s
  rw [StateT.run_bind, run_liftM]
  simp [map_bind]

@[simp]
lemma simulateQ_liftM_spec_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro) (hashSpec.query q) = ro q := by
  change simulateQ (unifFwdImpl hashSpec + ro)
    (liftM (liftM (hashSpec.query q) :
      OracleQuery (unifSpec + hashSpec) _)) = _
  simp [simulateQ_query]

lemma simulateQ_HasQuery_query (q : hashSpec.Domain) :
    simulateQ (unifFwdImpl hashSpec + ro)
      (HasQuery.query (spec := hashSpec)
        (m := OracleComp (unifSpec + hashSpec)) q) =
      ro q := by
  rw [HasQuery.instOfMonadLift_query]
  exact simulateQ_liftM_spec_query ro q

end roSim
