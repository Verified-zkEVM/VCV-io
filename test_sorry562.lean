import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.EvalDist

set_option autoImplicit false

open OracleSpec OracleComp ENNReal Finset

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0,0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

-- Prove that cachingOracle.withLogging t' has a nice run form
private lemma cachingOracle_withLogging_run_run (t' : spec.Domain) (cache₀ : QueryCache spec) :
    (cachingOracle.withLogging (spec := spec) t').run.run cache₀ =
    (cachingOracle (spec := spec) t').run cache₀ >>= fun uc =>
      pure ((uc.1, [⟨t', uc.1⟩]), uc.2) := by
  simp only [QueryImpl.withLogging_apply,
    WriterT.run_bind', WriterT.run_monadLift',
    StateT.run_bind, StateT.run_map]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext ⟨u, c⟩
  simp only [Prod.map, id_eq, WriterT.run_bind', WriterT.run_tell, WriterT.run_pure',
    StateT.run_pure, map_pure, List.nil_append, List.append_nil, pure_bind]

-- Now use this to analyze support
private lemma cachingOracle_withLogging_support
    (t' : spec.Domain) (cache₀ : QueryCache spec)
    (z : (spec.Range t' × QueryLog spec) × QueryCache spec)
    (hz : z ∈ support ((cachingOracle.withLogging (spec := spec) t').run.run cache₀)) :
    z.1.2 = [⟨t', z.1.1⟩] ∧
    (z.1.1, z.2) ∈ support ((cachingOracle (spec := spec) t').run cache₀) := by
  rw [cachingOracle_withLogging_run_run] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨⟨u, c⟩, hmem, hpure⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst hpure
  exact ⟨rfl, hmem⟩
