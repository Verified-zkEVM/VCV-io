import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.EvalDist

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0,0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

example (t' : spec.Domain) (cache₀ : QueryCache spec)
    (u' : spec.Range t') (w₁ : QueryLog spec) (cache₁ : QueryCache spec)
    (hstep1 : ((u', w₁), cache₁) ∈ support
      ((cachingOracle.withLogging (spec := spec) t').run.run cache₀)) :
    w₁ = [⟨t', u'⟩] := by
  simp only [QueryImpl.withLogging_apply, WriterT.run_bind',
    WriterT.run_monadLift', WriterT.run_tell,
    StateT.run_bind, StateT.run_map, StateT.run_pure,
    support_bind, support_map, support_pure,
    Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff,
    Prod.map, id_eq] at hstep1
  have : Nat := hstep1
  sorry
