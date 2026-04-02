/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.SimSemantics.Append

/-!
# Message Authentication Codes

This file defines keyed message-authentication-code algorithms together with their standard
UF-CMA security game.
-/

universe u v

open OracleSpec OracleComp ENNReal

/-- MAC algorithm with computations in the monad `m`, where `M` is the message space, `K` the key
space, and `T` the tag space. -/
structure MacAlg (m : Type → Type v) [Monad m] (M K T : Type) where
  keygen : m K
  tag : K → M → m T
  verify : K → M → T → m Bool

namespace MacAlg
section taggingOracle

variable {m : Type → Type v} [Monad m] {M K T : Type}

/-- Oracle exposing chosen-message tagging queries while logging every queried message. -/
def taggingOracle (macAlg : MacAlg m M K T) (k : K) :
    QueryImpl (M →ₒ T) (WriterT (QueryLog (M →ₒ T)) m) :=
  QueryImpl.withLogging (fun msg => macAlg.tag k msg)

end taggingOracle

section sound

variable {m : Type → Type v} [Monad m] {M K T : Type}

/-- Perfect completeness for a MAC: honestly generated tags always verify. -/
def PerfectlyComplete (macAlg : MacAlg m M K T) (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, Pr[= true | runtime.evalDist do
    let k ← macAlg.keygen
    let τ ← macAlg.tag k msg
    macAlg.verify k msg τ] = 1

end sound

section UF_CMA

variable {ι : Type u} {spec : OracleSpec ι} {M K T : Type}
  [DecidableEq M] [DecidableEq T]

/-- UF-CMA adversary for a MAC: it receives oracle access to the tagging oracle and outputs a
candidate forgery `(msg, tag)`. -/
structure UF_CMA_Adversary (_macAlg : MacAlg (OracleComp spec) M K T) where
  main : OracleComp (spec + (M →ₒ T)) (M × T)

/-- UF-CMA experiment for a MAC: the adversary succeeds iff it outputs a valid tag for a fresh
message under the challenge key. -/
def UF_CMA_Exp {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) : SPMF Bool :=
  runtime.evalDist do
    let k ← macAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ T))
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) +
        macAlg.taggingOracle k
    let sim_adv : WriterT (QueryLog (M →ₒ T)) (OracleComp spec) (M × T) :=
      simulateQ impl adversary.main
    let ((msg, τ), log) ← sim_adv.run
    let verified ← macAlg.verify k msg τ
    return !log.wasQueried msg && verified

/-- UF-CMA advantage for a MAC, represented as the probability of producing a valid forgery on a
fresh message. -/
noncomputable def UF_CMA_Advantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) : ℝ≥0∞ :=
  Pr[= true | UF_CMA_Exp runtime adversary]

end UF_CMA

end MacAlg
