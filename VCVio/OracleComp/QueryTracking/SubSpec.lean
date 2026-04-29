/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Query bounds and oracle-spec inclusions

This file contains preservation lemmas for structural query bounds under
`SubSpec` lifting.
-/

open OracleSpec

universe u

namespace OracleComp

variable {ι τ : Type u}
variable {spec : OracleSpec ι} {superSpec : OracleSpec τ}
variable {α : Type u}

/-- Predicate-targeted query bounds are preserved by lifting along a `SubSpec`
when the target predicate agrees with the source predicate on lifted queries.

No `LawfulSubSpec` assumption is needed: query bounds only inspect query indices,
not the distribution of responses. -/
theorem IsQueryBoundP.liftComp_subSpec
    [h : spec ⊂ₒ superSpec]
    {oa : OracleComp spec α}
    {p : spec.Domain → Prop} [DecidablePred p]
    {q : superSpec.Domain → Prop} [DecidablePred q]
    {n : ℕ}
    (hpq : ∀ t, p t ↔ q (h.onQuery t))
    (hoa : oa.IsQueryBoundP p n) :
    (liftComp oa superSpec).IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
      simp
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at hoa
      rw [liftComp_bind, liftComp_query]
      change IsQueryBoundP
        ((liftM (spec.query t) : OracleComp superSpec (spec.Range t)) >>=
          fun u => liftComp (mx u) superSpec) q n
      rw [show
          (liftM (spec.query t) : OracleComp superSpec (spec.Range t)) =
            liftM (superSpec.query (h.onQuery t)) >>= fun u =>
              pure (h.onResponse t u) by
        change ((liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) :
            OracleComp superSpec (spec.Range t)) =
          (liftM (superSpec.query (h.onQuery t)) >>= fun u =>
            pure (h.onResponse t u))
        rw [show
            (liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) =
              ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _]
        rfl]
      rw [bind_assoc, isQueryBoundP_query_bind_iff]
      constructor
      · simpa [← hpq t] using hoa.1
      · intro u
        rw [pure_bind]
        have hcont := ih (h.onResponse t u) (hoa.2 (h.onResponse t u))
        by_cases hp : p t
        · have hq : q (h.onQuery t) := (hpq t).1 hp
          simpa [hp, hq] using hcont
        · have hq : ¬ q (h.onQuery t) := fun hqt => hp ((hpq t).2 hqt)
          simpa [hp, hq] using hcont

end OracleComp
