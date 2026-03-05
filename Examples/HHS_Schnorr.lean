/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.FiatShamir

/-!
# Schnorr Sigma Protocol over Hard Homogeneous Spaces

Defines the simplest (single-bit challenge) Schnorr-like Σ-protocol for knowledge of
discrete log in an additive torsor, and states the standard security properties.

## Protocol

Given `(x₀, pk) : P × P` with witness `sk : G` satisfying `sk +ᵥ x₀ = pk`:

1. **Commit**: sample `r ← G`, output `(r +ᵥ pk, r)` as `(PC, SC)`
2. **Challenge**: receive `b : Bool`
3. **Respond**: if `b` then `r` else `r + sk`
4. **Verify**: check `z +ᵥ (if b then pk else x₀) = PC`

Special soundness extracts `sk = z₂ - z₁` from two accepting transcripts with
`b₁ = true, b₂ = false`.
-/

set_option autoImplicit false

open OracleSpec OracleComp SigmaProtocol

variable (G P : Type)
  [AddCommGroup G] [AddTorsor G P]
  [SampleableType G] [SampleableType P] [DecidableEq P]
  [unifSpec.Fintype] [unifSpec.Inhabited]

/-- Schnorr-like Σ-protocol over an HHS (additive torsor). Challenge space is `Bool`. -/
def schnorrSigma : SigmaProtocol (P × P) G P G Bool G
    (fun stmt sk => decide (sk +ᵥ stmt.1 = stmt.2)) where
  commit stmt _sk := do
    let r ← $ᵗ G
    return (r +ᵥ stmt.2, r)
  respond _stmt sk sc b := pure (if b then sc else sc + sk)
  verify stmt pc b z := if b then decide (z +ᵥ stmt.2 = pc) else decide (z +ᵥ stmt.1 = pc)
  sim _stmt := $ᵗ P
  extract b₁ z₁ b₂ z₂ := pure (if b₁ then z₂ - z₁ else z₁ - z₂)

/-! ## Security properties -/

theorem schnorrSigma_complete :
    PerfectlyComplete (schnorrSigma G P) := by
  sorry

theorem schnorrSigma_speciallySound :
    SpeciallySound (schnorrSigma G P) := by
  sorry

/-- Full transcript simulator: pick `b`, pick `z`, compute commitment from verification eq. -/
noncomputable def schnorrSimTranscript (stmt : P × P) : ProbComp (P × Bool × G) := do
  let b ← $ᵗ Bool
  let z ← $ᵗ G
  let pc := if b then z +ᵥ stmt.2 else z +ᵥ stmt.1
  return (pc, b, z)

theorem schnorrSigma_hvzk :
    HVZK (schnorrSigma G P) (schnorrSimTranscript G P) := by
  sorry
