/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import Examples.Schnorr.SigmaProtocol
import VCVio.CryptoFoundations.FiatShamir.Sigma.Security
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Schnorr Signature via Fiat-Shamir: an end-to-end EUF-CMA proof

An end-to-end EUF-CMA reduction for the Schnorr digital signature, exercising
the main composition layers of the VCVio framework on a single concrete
scheme:

* a Σ-protocol (`Examples/Schnorr/SigmaProtocol.lean`),
* the generic Fiat-Shamir transform
  (`VCVio/CryptoFoundations/FiatShamir/Sigma.lean`),
* the replay-based forking lemma
  (`VCVio/CryptoFoundations/ReplayFork.lean` and
  `VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`),
* special-soundness extraction
  (`VCVio/CryptoFoundations/SigmaProtocol.lean`),
* and the discrete-log hardness assumption
  (`VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`).

## Construction

Given `Module F G`, a generator `g : G`, and a bijection
`hg : Function.Bijective (· • g : F → G)` (i.e. `F` acts simply transitively on
`G` via `g`):

* **Key generation**: sample `sk ← $ᵗ F`, output `(pk, sk) = (sk • g, sk)`.
* **Sign**: commit `R = r • g`, hash `c = H(m, R)`, respond `z = r + c · sk`.
* **Verify**: re-derive `c = H(m, R)` via the random oracle and check
  `z • g = R + c • pk`.

## Security: the bound

Let `ε := A.advantage` be the EUF-CMA advantage of an adversary `A` making at
most `qS` signing-oracle queries and `qH` random-oracle queries against the
random-oracle runtime `FiatShamir.runtime`. Define

```
ε' := ε  -  qS · (qS + qH) / |F|
```

(`ENNReal` subtraction, which truncates at zero; whenever the simulation
overhead exceeds `ε`, the bound is trivially satisfied). Then there is a DLog
reduction `B : DLogAdversary F G` such that

```
ε' · ( ε' / (qH + 1)  -  1 / |F| )   ≤   Pr[ B succeeds in dlogExp g ].
```

This is the Pointcheval-Stern bound with quantitative HVZK plugged in at
`ζ_zk = 0` (Schnorr has perfect HVZK) and the simulator's commit-predictability
plugged in at `β = 1/|F|` (the Schnorr simulator's commitment is uniform on
`G` whenever `F` acts simply transitively on `G` via `g`, since
`Fintype.card G = Fintype.card F`).

The denominator `qH + 1` is the textbook Pointcheval-Stern denominator for a
source adversary with `qH` random-oracle queries. The reduction wraps the
adversary so that the forgery's hash point is always among the forkable
positions: it appends one explicit `(message, commit)` query for the forgery's
hash point on top of the source's `qH` queries, and applies the replay-forking
lemma at fork slot parameter `qH`. The framework's `Fork.forkPoint qH` indexes
`Fin (qH + 1)`, providing exactly enough slots for the wrapped adversary's
`qH + 1` total queries (no double-counting). As a result, the bound is
*unconditional* in `pk`: there is no remaining "verifier guesses a uniform
challenge" term that would have to be discharged separately for keys on which
verification is independent of the challenge.

## Glossary

* `signHashQueryBound oa qS qH`: the source EUF-CMA adversary `oa` issues at
  most `qS` signing-oracle queries and `qH` random-oracle queries.
* `Fork.advantage`: the managed-RO NMA advantage strengthened by the
  structural condition that the forgery's hash point appears in the live
  random-oracle log (i.e. the forking lemma can rewind it).
* `FiatShamir.runtime`: the random-oracle runtime under which the EUF-CMA
  experiment runs (caching random oracle starting from an empty cache,
  composed with public uniform sampling).

## Proof chain

`signature_euf_cma` (this file)

  ↓ instantiates

`FiatShamir.euf_cma_bound`
(`VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean`)

  ↓ composes

* `cma_to_nma_advantage_bound`: CMA → managed-RO NMA via HVZK simulation
  (`Sigma/Reductions.lean` → `Sigma/Stateful/Chain.lean`);
* `nma_to_hard_relation_bound`: managed-RO NMA → witness extraction via the
  replay-forking lemma `Fork.replayForkingBound`
  (`Sigma/Reductions.lean` → `Sigma/Fork.lean` → `ReplayFork.lean`)
  and special soundness `SigmaProtocol.extract_sound_of_speciallySoundAt`.

The Schnorr-specific inputs are exactly:

* `Schnorr.sigma_speciallySound`        — the `(z₁ - z₂) · (c₁ - c₂)⁻¹`
                                          extractor;
* `Schnorr.sigma_hvzk`                  — perfect HVZK (`ζ_zk = 0`);
* `Schnorr.sigma_simCommitPredictability` — the simulator's commit is uniform
                                          on `G`, giving `β = 1/|F|`.
-/


open OracleComp OracleSpec DiffieHellman
open scoped ENNReal

namespace Schnorr

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- Schnorr signature scheme: Fiat-Shamir applied to the Schnorr Σ-protocol
with the discrete-log generable relation. The construction itself does not
require a bijection between `F` and `G` via `· • g`; that hypothesis is only
needed at the security theorem `signature_euf_cma`. -/
def signature (g : G) (M : Type) [DecidableEq M] :
    SignatureAlg (OracleComp (unifSpec + (M × G →ₒ F)))
      (M := M) (PK := G) (SK := F) (S := G × F) :=
  FiatShamir (Schnorr.sigma F G g) (dlogGenerable (F := F) g) M

omit [Fintype F] in
/-- Completeness of the Schnorr signature follows from completeness of the
underlying Schnorr Σ-protocol via the generic Fiat-Shamir completeness theorem. -/
theorem signature_complete (g : G) (M : Type) [DecidableEq M] :
    SignatureAlg.PerfectlyComplete
      (signature F G g M)
      (FiatShamir.runtime (Commit := G) (Chal := F) M) :=
  FiatShamir.perfectlyCorrect _ _ M (Schnorr.sigma_complete F G g)

omit [Fintype F] [SampleableType G] in
/-- The DLog hard-relation experiment (`hardRelationExp` for `dlogGenerable`)
and the textbook DLog experiment (`dlogExp`) are the same probability, given
the bijection `· • g : F → G`. The factor of `g` ignored by the lifted
`fun _ pk => red pk` reduction is harmless because `dlogExp` re-supplies it. -/
private theorem hardRelationExp_dlogGenerable_eq_dlogExp
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (red : G → ProbComp F) :
    Pr[= true | hardRelationExp (dlogGenerable (F := F) g) red] =
    Pr[= true | dlogExp g (fun _ pk => red pk)] := by
  rw [show Pr[= true | hardRelationExp (dlogGenerable (F := F) g) red] =
      Pr[= true | do
        let x ← $ᵗ F
        let w ← red (x • g)
        pure (decide (w • g = x • g))] by
    simp [hardRelationExp, dlogGenerable]]
  exact probOutput_bind_congr' _ true fun x =>
    probOutput_bind_congr' _ true fun sk => by simp [hg.1.eq_iff]

/-- **EUF-CMA reduction for Schnorr signatures (Pointcheval-Stern).**

The bound is

```
ε' · ( ε' / (qH + 1)  -  1 / |F| )   ≤   Pr[ reduction succeeds in dlogExp g ],
ε' := ε  -  qS · (qS + qH) / |F|,
```

where `ε := adv.advantage (FiatShamir.runtime M)` is the EUF-CMA advantage and
`qS`, `qH` upper-bound the signing-oracle and random-oracle queries. This is
the textbook Pointcheval-Stern denominator: the Fiat-Shamir reduction wraps
the source adversary so the forgery's hash point is always among the forkable
positions, and the framework's `Fork.forkPoint qH` indexing in `Fin (qH + 1)`
provides exactly the right number of slots (source-`qH` queries plus the one
appended verifier-point query). See the module docstring for the full chain.

Three Schnorr-specific facts feed in:

* `Schnorr.sigma_speciallySound` — extractor `(z₁ - z₂) · (c₁ - c₂)⁻¹`;
* `Schnorr.sigma_hvzk` — perfect HVZK, so the per-query simulation loss
  `ζ_zk` vanishes;
* `Schnorr.sigma_simCommitPredictability` — the simulator's commit marginal
  is uniform on `G` whenever `F` acts simply transitively via `g`, giving
  the commit-collision bound `β = 1/|F|`.

The result is delivered in the textbook DLog form `dlogExp g reduction` via
the conversion `hardRelationExp_dlogGenerable_eq_dlogExp`. -/
theorem signature_euf_cma (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M]
    (adv : SignatureAlg.unforgeableAdv (signature F G g M))
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (Commit := G) (Chal := F)
      (S' := G × F) (oa := adv.main pk) qS qH) :
    ∃ reduction : DLogAdversary F G,
      let eps := adv.advantage (FiatShamir.runtime (Commit := G) (Chal := F) M) -
        ((qS : ENNReal) * (qS + qH) * ((Fintype.card F : ℝ≥0∞)⁻¹))
      eps * (eps / (qH + 1 : ENNReal) - FiatShamir.challengeSpaceInv F) ≤
        Pr[= true | dlogExp g reduction] := by
  haveI : Inhabited F := ⟨0⟩
  obtain ⟨red, hred⟩ := FiatShamir.euf_cma_bound
    (Schnorr.sigma F G g) (dlogGenerable (F := F) g) M
    (Schnorr.sigma_speciallySound F G g)
    (by intro ω₁ p₁ ω₂ p₂; simp [Schnorr.sigma])
    (Schnorr.simTranscript F G g)
    (ζ_zk := 0) le_rfl
    ((SigmaProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (Schnorr.sigma_hvzk F G g))
    (β := (Fintype.card F : ℝ≥0∞)⁻¹)
    (Schnorr.sigma_simCommitPredictability F G g hg)
    adv qS qH hQ
  simp only [mul_zero, ENNReal.ofReal_zero, zero_add] at hred ⊢
  exact ⟨fun _ pk => red pk,
    hred.trans (le_of_eq (hardRelationExp_dlogGenerable_eq_dlogExp F G g hg red))⟩

#print axioms signature_euf_cma

end Schnorr
