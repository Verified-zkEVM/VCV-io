/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Bridge

/-!
# Compatibility endpoints for the stateful Fiat-Shamir CMA proof

The main stateful proof path uses the full `CmaState` game definitions from
`Stateful.Games` and the full-state post-keygen normal form in
`Stateful.Bridge`.

The generic `SignatureAlg.unforgeableExp` experiment is still a useful public
API, but it interprets signing queries through a `WriterT` query log. Any theorem
equating that legacy public experiment with the full-state CMA game necessarily
relates two interpreters. Such theorems belong here, not in the main stateful
bridge.
-/

universe u v

open OracleSpec OracleComp ProbComp

namespace FiatShamir.Stateful

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
variable [SampleableType Chal]

/-! ## Public and stateful endpoints -/

/-- The legacy public EUF-CMA advantage exposed by `SignatureAlg`.

This endpoint uses `SignatureAlg.unforgeableExp`, which logs signing queries via
`WriterT`. It is kept separate from the full-state stateful proof path. -/
noncomputable def publicUnforgeableAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ENNReal :=
  adv.advantage (_root_.FiatShamir.runtime M)

/-- The full-state post-keygen CMA advantage used by the stateful proof path.

This is the key-generation wrapper around `postKeygenFreshProb`; the fixed-key
body runs through `cmaRealSourceFullSum` on `CmaState`. -/
noncomputable def statefulPostKeygenFreshAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ENNReal :=
  Pr[= true | ((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2)]

/-- The full-state CMA run as a Boolean freshness experiment.

This packages `cmaRealRun` with the same final freshness predicate as the
post-keygen normal form. -/
noncomputable def statefulCmaFreshExperiment
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ProbComp Bool := do
  let z ← cmaRealRun σ hr M adv
  let out := z.1
  let verified := z.2.1
  let signed := z.2.2
  pure (!decide (out.1 ∈ signed) && verified)

/-- The full-state CMA advantage obtained directly from `cmaRealRun`.

This endpoint is equivalent to `statefulPostKeygenFreshAdvantage` by unfolding
the public-key query in `signedAdv`; the equality is a stateful-game normal-form
fact and does not mention `SignatureAlg.unforgeableExp`. -/
noncomputable def statefulCmaFreshAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ENNReal :=
  Pr[= true | statefulCmaFreshExperiment σ hr M adv]

/-! ## Compatibility boundary -/

/-- Compatibility proposition between the legacy public experiment and the
full-state stateful experiment.

The main stateful proof path should assume or prove facts about
`statefulCmaFreshAdvantage`. If a caller needs the historical
`SignatureAlg.unforgeableAdv.advantage` API, the required normalization theorem
should target this proposition in this quarantined module. -/
def PublicCompatible
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : Prop :=
  publicUnforgeableAdvantage σ hr M adv =
    statefulCmaFreshAdvantage σ hr M adv

end FiatShamir.Stateful
