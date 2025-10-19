-- /-
-- Copyright (c) 2024 Devon Tuma. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Devon Tuma
-- -/
-- import Mathlib.Computability.TMComputable
-- import VCVio.OracleComp.OracleComp

-- /-!
-- # Polynomial Time Computations

-- Polynomial complexity for computations with oracles.

-- More background theory on `TM2ComputableInPolyTime` would be needed
-- to make this kind of approach usable in practice.

-- More adaptation would also be needed to handle dependent types
-- -/

-- open OracleSpec

-- namespace OracleComp

-- /-- Predicate for capturing polynomial complexity of an `OracleComp`.
-- Functions by extending the turing-machine definition from mathlib. -/
-- inductive PolyTimeOC {ι : Type} {spec : OracleSpec} :
--     {α β : Type} → (α → OracleComp spec β) → Prop
--   -- If computing the query input is poly-time then so is the query
--   | polyTime_query {α : Type} (i : ι) (f : α → spec.Domain)
--       (hf : Σ ea eb, Turing.TM2ComputableInPolyTime ea eb f) :
--     PolyTimeOC (λ x ↦ (query (f x) : OracleComp spec _))
--   -- Returning a poly-time value is also poly-time
--   | polyTime_return {α β : Type} (f : α → β)
--       (hf : Σ ea eb, Turing.TM2ComputableInPolyTime ea eb f) :
--     PolyTimeOC (λ x ↦ return (f x))
--   -- Binding two poly-time computations is poly-time
--   | polyTime_bind {α β γ : Type} (oa : α → OracleComp spec β)
--       (ob : α → β → OracleComp spec γ)
--       (hoa : PolyTimeOC oa) (hob : PolyTimeOC (Function.uncurry ob)) :
--     PolyTimeOC (λ x ↦ do let y ← oa x; ob x y)

-- end OracleComp
