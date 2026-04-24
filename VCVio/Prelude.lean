/-
Copyright (c) 2025 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import ToMathlib.General

/-!
# VCVio Prelude

Shared project-wide declarations and simp attributes imported throughout `VCVio`.
-/

declare_aesop_rule_sets [UnfoldEvalDist]

/-- Simp set for game-hopping proofs: evalDist, probOutput, simulateQ, wp, relTriple rules. -/
register_simp_attr game_rule

/-- Simp set for opening common query-handler definitions and run-shapes. -/
register_simp_attr handler_simp
