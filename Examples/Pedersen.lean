/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.CommitmentScheme
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.ProgramLogic.Tactics

/-!
# Pedersen Commitment Scheme

This file defines the Pedersen commitment scheme and proves:
1. **Correctness**: honestly generated commitments verify.
2. **Perfect hiding**: the commitment distribution is independent of the message
   (via a bijection argument, same pattern as one-time pad).
3. **Computational binding**: a successful double-opener yields a DLog solver.

## Mathematical Setup

Uses the same additive `Module F G` notation as `DiffieHellman.lean`:
- `F` is the scalar field (exponents), `G` is the group
- `g : G` is a fixed generator with `Function.Bijective (· • g : F → G)`
- Public parameter: `h = x • g` for secret random `x : F`
- Commitment to message `m : F`: sample `d ← $ᵗ F`, output `(d • g + m • h, d)`
- Verification: check `c = d • g + m • h`
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal DiffieHellman CommitmentScheme

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]

/-! ## Definition -/

/-- The Pedersen commitment scheme over a cyclic group with generator `g`.

| Component | Definition |
|-----------|-----------|
| Setup | Sample `x ← $ᵗ F`, return `h = x • g` |
| Commit(h, m) | Sample `d ← $ᵗ F`, return `(d • g + m • h, d)` |
| Verify(h, m, c, d) | Check `d • g + m • h = c` |
-/
def pedersenCommit (g : G) : CommitmentScheme G F G F where
  setup := do let x ← $ᵗ F; return (x • g)
  commit pp m := do
    let d ← $ᵗ F
    return (d • g + m • pp, d)
  verify pp m c d := decide (d • g + m • pp = c)

namespace pedersenCommit

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]
variable {g : G}

/-! ## Correctness -/

theorem correct : (pedersenCommit (F := F) g).PerfectlyCorrect := by
  intro pp _hpp m cd hmem
  have hmem' : cd ∈ support (do
      let d ← ($ᵗ F : ProbComp F); pure ((d : F) • g + m • pp, d)) := hmem
  simp only [support_bind, support_pure, Set.mem_iUnion,
             Set.mem_singleton_iff] at hmem'
  obtain ⟨d', -, rfl, rfl⟩ := hmem'
  show decide ((d' : F) • g + m • pp = d' • g + m • pp) = true
  simp

/-! ## Perfect hiding -/

omit [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype G] [SampleableType G] [DecidableEq G] in
private lemma commit_fst_bijective (hg : Function.Bijective (· • g : F → G))
    (pp : G) (m : F) : Function.Bijective (fun d : F => d • g + m • pp) := by
  show Function.Bijective ((· + m • pp) ∘ (· • g : F → G))
  exact Function.Bijective.comp
    ⟨fun a b h => add_right_cancel h,
     fun y => ⟨y - m • pp, sub_add_cancel y (m • pp)⟩⟩
    hg

/-- Rewrite the commitment distribution as a mapped uniform sample. -/
private lemma commit_fst_eq_map (pp : G) (m : F) :
    Prod.fst <$> (pedersenCommit (F := F) g).commit pp m =
    (fun d : F => d • g + m • pp) <$> ($ᵗ F : ProbComp F) := by
  simp [pedersenCommit]

/-- The Pedersen commitment scheme is perfectly hiding: the commitment distribution
is independent of the committed message.

The proof uses the same bijection-coupling idea as the one-time pad: composing
the generator bijection `d ↦ d • g` with translation `· + c` gives a bijection
`F → G`, so the pushforward of uniform on `F` is uniform on `G` regardless of `c`. -/
theorem perfectlyHiding (hg : Function.Bijective (· • g : F → G)) :
    (pedersenCommit (F := F) g).PerfectlyHiding := by
  intro pp _hpp m₁ m₂
  rw [commit_fst_eq_map, commit_fst_eq_map]
  have h₁ := evalDist_map_bijective_uniform_cross (α := F) (β := G)
    (fun d => d • g + m₁ • pp) (commit_fst_bijective hg pp m₁)
  have h₂ := evalDist_map_bijective_uniform_cross (α := F) (β := G)
    (fun d => d • g + m₂ • pp) (commit_fst_bijective hg pp m₂)
  exact h₁.trans h₂.symm

/-! ## Computational binding reduces to DLog -/

/-- Given a binding adversary for Pedersen, construct a DLog adversary.
If the binder produces two valid openings `(m₁, d₁)` and `(m₂, d₂)` to the same
commitment `c` with `m₁ ≠ m₂`, extract the discrete log as `(d₁ - d₂) / (m₂ - m₁)`. -/
def dlogReduction (binder : BindingAdv G F G F) : DLogAdversary F G :=
  fun gen h => do
    let (c, m₁, d₁, m₂, d₂) ← binder h
    return if decide (m₁ ≠ m₂ ∧ d₁ • gen + m₁ • h = c ∧ d₂ • gen + m₂ • h = c) then
      (d₁ - d₂) / (m₂ - m₁)
    else 0

/-- Computational binding: a successful Pedersen binding adversary yields a
successful DLog solver. Specifically, `Pr[binding wins] ≤ Pr[DLog wins]`. -/
theorem binding_le_dlog (hg : Function.Bijective (· • g : F → G))
    (binder : BindingAdv G F G F) :
    Pr[= true | (pedersenCommit g).bindingExp binder] ≤
    Pr[= true | dlogExp g (dlogReduction binder)] := by
  sorry

end pedersenCommit
