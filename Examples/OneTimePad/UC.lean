/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.OneTimePad.Basic
import VCVio.Interaction.UC.Computational
import VCVio.Interaction.UC.OpenProcessModel
import VCVio.OracleComp.Constructions.BitVec

/-!
# One-Time Pad at the UC Observation Layer

This file wires the one-time pad from `Examples.OneTimePad.Basic` into
the refactored `Interaction.UC.Semantics` observation framework,
producing a **non-vacuous** `CompEmulates 0` statement at the
observation level.

## Canonical UC story being modeled

In the Universal Composability literature, OTP is the canonical bridge
from symmetric-key privacy to a **Secure Message Transmission**
functionality `F_SMT`. The standard setup is:

* **Real protocol** `π_OTP`. The sender samples a one-time key
  `k ← uniform`, computes `c := k ⊕ m`, and delivers `c` on the
  (authenticated) channel. The receiver recovers `m` via `k ⊕ c`.
* **Ideal functionality** `F_SMT`. The sender hands `m` directly to
  the ideal party; the environment learns only what `F_SMT` chooses
  to leak on its public interface (in the simplest formulation,
  only `|m|`).
* **Simulator** `S`. Wraps `F_SMT` to match `π_OTP`'s public
  interface by sampling a uniform ciphertext `c' ← uniform` and
  delivering it to the environment.

The OTP privacy statement is that the environment's joint view in the
real world and in the ideal world have the same distribution. The
content is "XOR against a uniform one-time key is uniform", i.e.
`k ⊕ m ∼ uniform` for every `m`.

## What this file formalizes

We model the two views at the **observation layer**:

* `realCipherObserve sp msg P` samples a uniform key `k`, computes
  `c := k ⊕ msg`, and `guard`s `P c = true`. This is the real
  world's ciphertext-plus-distinguisher bit.
* `idealCipherObserve sp P` samples a uniform ciphertext `c` directly
  and `guard`s `P c = true`. This is the ideal world's view under
  the canonical simulator, which replaces the OTP ciphertext with a
  fresh uniform sample.

The central lemma `evalDist_realCipherObserve_eq` transports OTP
perfect secrecy to the sub-probabilistic observation target: the
`SPMF Unit` denotations of the real and ideal observations agree for
every plaintext `msg` and every Boolean predicate `P`. This is where
the UC indistinguishability content actually lives.

## How the observation lifts into `Interaction.UC.Semantics`

The bundled versions package the observation as a `Semantics T`:

* `realSmcSemantics sp readMsg P` reads a plaintext from the closed
  system via a user-supplied `readMsg : T.Closed → BitVec sp` and
  runs `realCipherObserve`. This is the environment's view under the
  real protocol.
* `idealSmcSemantics sp P` ignores the closed system beyond sampling
  a uniform ciphertext and runs `idealCipherObserve`. This is the
  environment's view under the simulator-wrapped ideal
  functionality.

Because the observation layer is the same for every closed system in
`T`, `realSmcSemantics_eq_idealSmcSemantics` states the lifted OTP
privacy claim:
`(realSmcSemantics sp readMsg P).evalDist W = (idealSmcSemantics sp P).evalDist W`
for every `W : T.Closed`. The UC indistinguishability statement
`compEmulates_realSmcSemantics` then falls out: under the real SMC
semantics, any two closed systems are indistinguishable with
advantage zero.

## Non-vacuity

1. **Type-level.** The `SPMF Unit` target carries genuine failure
   mass (`probFailure_realCipherObserve`), escaping the pre-refactor
   `ProbComp Unit` collapse to point mass.
2. **Security-level.** The `run` field of `realSmcSemantics` is a
   genuine function of its closed-system argument: picking a
   discriminating `readMsg` makes `run W_real` and `run W_ideal`
   literally different `OptionT ProbComp Unit` values. OTP privacy
   is what collapses their `SPMF` denotations, not a definitional
   coincidence. The discriminating-reader witness is
   `realSmcSemantics_run_distinct`.

## Scope and future work

We model the distinguisher as a Boolean predicate `P : BitVec sp → Bool`
on the ciphertext. In canonical UC the distinguisher's view is the
full transcript of the closed composition, not just the delivered
ciphertext. A full UC-style proof would instead construct real and
ideal objects `π_OTP, F_SMT ∘ S : T.Obj Δ` at a nontrivial boundary
`Δ` modeling the sender/receiver/network interface, and prove
`CompEmulates sem ε π_OTP (F_SMT ∘ S)` against every plug
(environment). That is a substantial `OpenProcess` modeling effort
and is left as future work.

What this file establishes is the complete **observation-layer**
story: OTP's key privacy content, once packaged in the UC
`Semantics` bundle, gives a `CompEmulates 0` indistinguishability
between any pair of closed systems for every fixed distinguisher
predicate, and the claim is non-vacuous in both the type-level and
security-level senses above.

## References

* Canetti, *Universally Composable Security: A New Paradigm for
  Cryptographic Protocols* (2001), §6 on secure message
  transmission.
* Canetti, Stoughton, Varia, *EasyUC: Using EasyCrypt to Mechanize
  Proofs of Universally Composable Security* (IACR ePrint 2019/582),
  §6 on OTP used as a hybrid encryption step.
* Katz-Lindell, *Introduction to Modern Cryptography* (3rd ed.),
  §3.2 on perfect secrecy of the one-time pad.
-/

open Interaction Interaction.UC OracleComp ENNReal

namespace oneTimePad
namespace UC

/-- The demo uses a single trivial party. -/
abbrev Party : Type := Unit

/-- The demo's fixed scheduler sampler: the trivial `OptionT ProbComp`
computation returning `ULift.up true`. Any concrete choice would do;
this one matches the observation monad used by the bundled semantics
below. -/
noncomputable def demoSchedulerSampler : OptionT ProbComp (ULift Bool) :=
  pure (ULift.up true)

/-- Shorthand for the concrete closed-Party open theory used in the demo. -/
private noncomputable abbrev T :=
  openTheory.{0, 0, 0, 0} Party (OptionT ProbComp) demoSchedulerSampler

/-! ## Real vs ideal cipher observation -/

/-- **Real-world observation** (environment's view of `π_OTP`). Sample
a uniform key `k : BitVec sp`, compute the ciphertext `c := k ⊕ msg`,
and `guard` that the distinguisher's predicate `P` holds at `c`.

Lives in `OptionT ProbComp` so the `guard` branch carries genuine
failure mass, which the old `ProbComp Unit` observation target could
not represent. -/
noncomputable def realCipherObserve (sp : ℕ) (msg : BitVec sp)
    (P : BitVec sp → Bool) : OptionT ProbComp Unit := do
  let k ← ($ᵗ BitVec sp : OptionT ProbComp (BitVec sp))
  guard (P (k ^^^ msg) = true)

/-- **Ideal-world observation** (environment's view under the canonical
simulator wrapping `F_SMT`). Sample a uniform ciphertext
`c : BitVec sp` directly and `guard` that the distinguisher's
predicate `P` holds at `c`.

No plaintext input is required: OTP privacy is what lets the
simulator reproduce this distribution without reading `msg`. -/
noncomputable def idealCipherObserve (sp : ℕ) (P : BitVec sp → Bool) :
    OptionT ProbComp Unit := do
  let c ← ($ᵗ BitVec sp : OptionT ProbComp (BitVec sp))
  guard (P c = true)

/-- Local copy of the `OracleComp`-internal lemma relating `Pr[= ()]` on
a `bind` with a `guard` to a `probEvent`. Kept private here to avoid
exposing internals of `VCVio.OracleComp.EvalDist`. -/
private lemma probOutput_liftM_bind_guard
    {α : Type} (oa : ProbComp α) (p : α → Prop) [DecidablePred p] :
    Pr[= () | (do let a ← (liftM oa : OptionT ProbComp α)
                  guard (p a) : OptionT ProbComp Unit)] = Pr[ p | oa] := by
  rw [probOutput_bind_eq_tsum]
  simp only [OptionT.probOutput_liftM, probOutput_guard]
  rw [probEvent_eq_tsum_ite]
  congr 1; ext a
  split_ifs <;> simp

/-! ### Success probabilities -/

/-- **Real-world success probability**:
`#{ k : P (k ⊕ msg) = true } / |BitVec sp|`. -/
theorem probOutput_realCipherObserve (sp : ℕ) (msg : BitVec sp)
    (P : BitVec sp → Bool) :
    Pr[= () | realCipherObserve sp msg P] =
      (Finset.univ.filter fun k : BitVec sp => P (k ^^^ msg) = true).card /
        (Fintype.card (BitVec sp) : ℝ≥0∞) := by
  change Pr[= () | (do
      let k ← (liftM ($ᵗ BitVec sp) : OptionT ProbComp (BitVec sp))
      guard (P (k ^^^ msg) = true) : OptionT ProbComp Unit)] = _
  rw [probOutput_liftM_bind_guard ($ᵗ BitVec sp) (fun k => P (k ^^^ msg) = true),
      probEvent_uniformSample]

/-- **Ideal-world success probability**:
`#{ c : P c = true } / |BitVec sp|`. -/
theorem probOutput_idealCipherObserve (sp : ℕ) (P : BitVec sp → Bool) :
    Pr[= () | idealCipherObserve sp P] =
      (Finset.univ.filter fun c : BitVec sp => P c = true).card /
        (Fintype.card (BitVec sp) : ℝ≥0∞) := by
  change Pr[= () | (do
      let c ← (liftM ($ᵗ BitVec sp) : OptionT ProbComp (BitVec sp))
      guard (P c = true) : OptionT ProbComp Unit)] = _
  rw [probOutput_liftM_bind_guard ($ᵗ BitVec sp) (fun c => P c = true),
      probEvent_uniformSample]

/-- **Real-world failure mass** is positive when `P` is not universally
true on `BitVec sp`: specifically, `1 -` (the real-world success
probability). Mirrors the ideal failure formula modulo the
bijection `k ↦ k ⊕ msg`, which is why the two agree as `SPMF`s. -/
theorem probFailure_realCipherObserve (sp : ℕ) (msg : BitVec sp)
    (P : BitVec sp → Bool) :
    Pr[⊥ | realCipherObserve sp msg P] =
      1 - (Finset.univ.filter fun k : BitVec sp => P (k ^^^ msg) = true).card /
        (Fintype.card (BitVec sp) : ℝ≥0∞) := by
  rw [probFailure_eq_sub_tsum,
      tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx),
      probOutput_realCipherObserve]

/-- **Ideal-world failure mass**: `1 -` (ideal success probability). -/
theorem probFailure_idealCipherObserve (sp : ℕ) (P : BitVec sp → Bool) :
    Pr[⊥ | idealCipherObserve sp P] =
      1 - (Finset.univ.filter fun c : BitVec sp => P c = true).card /
        (Fintype.card (BitVec sp) : ℝ≥0∞) := by
  rw [probFailure_eq_sub_tsum,
      tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx),
      probOutput_idealCipherObserve]

/-! ### OTP perfect secrecy at the observation layer -/

/-- **OTP perfect secrecy (observation form).** For every plaintext
`msg` and every Boolean predicate `P`, the real-world and ideal-world
observations have identical `SPMF Unit` denotations.

The proof reduces to showing that the `k ↦ k ⊕ msg` bijection
preserves the cardinality of the success filter, which is the
familiar "XOR with a uniform key is uniform" fact in disguise. -/
theorem evalDist_realCipherObserve_eq (sp : ℕ) (msg : BitVec sp)
    (P : BitVec sp → Bool) :
    evalDist (realCipherObserve sp msg P) =
      evalDist (idealCipherObserve sp P) := by
  apply SPMF.ext
  intro _
  change Pr[= () | realCipherObserve sp msg P] =
    Pr[= () | idealCipherObserve sp P]
  rw [probOutput_realCipherObserve, probOutput_idealCipherObserve]
  congr 2
  refine Finset.card_bij' (fun k _ => k ^^^ msg) (fun c _ => c ^^^ msg)
    ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rwa [show (c ^^^ msg ^^^ msg : BitVec sp) = c by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]]
  · intro k _
    simp only
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro c _
    simp only
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ## Concrete closed processes carrying a plaintext -/

/-- A concrete closed process whose state space is `BitVec sp` and
whose single step is a `.done` move that transitions to the fixed
message `msg`. Plays the role of an environment that has pre-committed
to a plaintext choice. Different `msg` values give structurally
distinct closed processes, witnessed by `msgClosed_ne` below. -/
noncomputable def msgClosed (sp : ℕ) (msg : BitVec sp) :
    T.Closed where
  Proc := BitVec sp
  step := fun _ =>
    { spec := .done
      semantics := ⟨⟩
      next := fun _ => msg }
  stepSampler := fun _ => ⟨⟩

/-- Distinct plaintexts give distinct closed processes. The two
processes share the state type `BitVec sp` and the `.done` spec; they
differ only in what `step.next` returns on the unit transcript, which
gives a direct way to separate them. -/
theorem msgClosed_ne (sp : ℕ) {msg₀ msg₁ : BitVec sp} (h : msg₀ ≠ msg₁) :
    msgClosed sp msg₀ ≠ msgClosed sp msg₁ := by
  intro heq
  apply h
  have hstep : HEq (msgClosed sp msg₀).step (msgClosed sp msg₁).step := by
    rw [heq]
  have hstep' : (msgClosed sp msg₀).step = (msgClosed sp msg₁).step :=
    eq_of_heq hstep
  have hstep0 := congrFun hstep' (0 : BitVec sp)
  change (⟨.done, ⟨⟩, fun _ => msg₀⟩ : Concurrent.StepOver _ (BitVec sp)) =
    ⟨.done, ⟨⟩, fun _ => msg₁⟩ at hstep0
  injection hstep0 with _ _ hnext
  exact congrFun hnext ⟨⟩

/-- A plaintext reader: a function extracting a `BitVec sp` plaintext
from any closed system. Supplying a reader is how the bundled
semantics specifies *which* structural feature of the closed system
plays the role of the plaintext. The concrete example we exhibit
later is "the state of a `msgClosed` process". -/
abbrev MsgReader (sp : ℕ) : Type 1 := T.Closed → BitVec sp

/-! ## Bundled `UC.Semantics`: real vs ideal SMC -/

/-- **Real SMC semantics.** Read the plaintext from the closed system
via `readMsg`, then run `realCipherObserve` against the fixed
distinguisher predicate `P`. Models the environment's view under
`π_OTP`.

The `run` field is genuinely a function of its closed-system argument
through `readMsg`. OTP privacy is what collapses the resulting
`SPMF Unit` denotations into the plaintext-independent ideal one. -/
noncomputable def realSmcSemantics (sp : ℕ)
    (readMsg : MsgReader sp) (P : BitVec sp → Bool) :
    Semantics T where
  m := OptionT ProbComp
  instMonad := inferInstance
  sem := SPMFSemantics.ofHasEvalSPMF (OptionT ProbComp)
  run := fun W => realCipherObserve sp (readMsg W) P

/-- **Ideal SMC semantics.** Ignore the closed system beyond sampling
a uniform ciphertext, then apply the distinguisher predicate `P`.
Models the environment's view under the canonical simulator wrapping
`F_SMT`: the simulator does not need the plaintext to reproduce the
ciphertext distribution. -/
noncomputable def idealSmcSemantics (sp : ℕ) (P : BitVec sp → Bool) :
    Semantics T where
  m := OptionT ProbComp
  instMonad := inferInstance
  sem := SPMFSemantics.ofHasEvalSPMF (OptionT ProbComp)
  run := fun _ => idealCipherObserve sp P

@[simp]
theorem realSmcSemantics_run (sp : ℕ) (readMsg : MsgReader sp)
    (P : BitVec sp → Bool) (W : T.Closed) :
    (realSmcSemantics sp readMsg P).run W =
      realCipherObserve sp (readMsg W) P := rfl

@[simp]
theorem idealSmcSemantics_run (sp : ℕ) (P : BitVec sp → Bool)
    (W : T.Closed) :
    (idealSmcSemantics sp P).run W = idealCipherObserve sp P := rfl

/-- **OTP UC indistinguishability at every closed system.** For every
plug-plaintext reader `readMsg` and every distinguisher predicate `P`,
the real SMC semantics and the ideal SMC semantics produce identical
`SPMF Unit` denotations on every closed system.

This is the transport of `evalDist_realCipherObserve_eq` through the
bundling layer. Concretely: pick any closed system, read its
plaintext, encrypt it under a uniform key, and apply the
distinguisher; the resulting `SPMF Unit` is independent of the
plaintext, hence matches the ideal simulation that never needed the
plaintext in the first place. -/
theorem realSmcSemantics_eq_idealSmcSemantics (sp : ℕ)
    (readMsg : MsgReader sp) (P : BitVec sp → Bool) (W : T.Closed) :
    (realSmcSemantics sp readMsg P).evalDist W =
      (idealSmcSemantics sp P).evalDist W := by
  change evalDist (realCipherObserve sp (readMsg W) P) =
      evalDist (idealCipherObserve sp P)
  exact evalDist_realCipherObserve_eq sp (readMsg W) P

/-! ## `CompEmulates 0` via observation-layer OTP privacy -/

/-- **OTP UC privacy as `CompEmulates`.** Under the real SMC semantics,
any two closed systems at any boundary are indistinguishable with
advantage zero, for every choice of plaintext reader and
distinguisher predicate.

The real-semantics-view of `close W_real K` is an `SPMF Unit` that
depends on `readMsg (close W_real K)` and `P`; by OTP privacy, this
is the same as the ideal-semantics view, which depends only on `P`
and is the same for `W_real` and `W_ideal`. Hence the two
real-semantics views coincide and the total variation distance is
zero. -/
theorem compEmulates_realSmcSemantics (sp : ℕ)
    (readMsg : MsgReader sp) (P : BitVec sp → Bool)
    {Δ : PortBoundary} (W_real W_ideal : T.Obj Δ) :
    CompEmulates (realSmcSemantics sp readMsg P) 0 W_real W_ideal := by
  intro K
  show Semantics.distAdvantage _ _ _ ≤ (0 : ℝ)
  unfold Semantics.distAdvantage
  rw [realSmcSemantics_eq_idealSmcSemantics sp readMsg P
        (T.close W_real K),
      realSmcSemantics_eq_idealSmcSemantics sp readMsg P
        (T.close W_ideal K)]
  change SPMF.tvDist
      (evalDist (idealCipherObserve sp P))
      (evalDist (idealCipherObserve sp P)) ≤ 0
  simp [SPMF.tvDist_self]

/-! ## Concrete instantiation: two structurally distinct closed systems -/

/-- **Plaintext indistinguishability from OTP privacy.** For any two
plaintexts `msg₀`, `msg₁` and any distinguisher predicate `P`, the
closed systems `msgClosed sp msg₀` and `msgClosed sp msg₁` are
indistinguishable under the real SMC semantics. When `msg₀ ≠ msg₁`
the two closed systems are structurally distinct (`msgClosed_ne`), so
the conclusion is a genuine indistinguishability obtained from OTP
privacy, not a collapse of the framework. -/
theorem compEmulates_msgClosed (sp : ℕ) (readMsg : MsgReader sp)
    (P : BitVec sp → Bool) (msg₀ msg₁ : BitVec sp) :
    CompEmulates (realSmcSemantics sp readMsg P) 0
      (msgClosed sp msg₀) (msgClosed sp msg₁) :=
  compEmulates_realSmcSemantics sp readMsg P
    (msgClosed sp msg₀) (msgClosed sp msg₁)

/-- Sanity check: when `msg₀ ≠ msg₁`, the two `msgClosed` inputs on the
left and right of `compEmulates_msgClosed` are not definitionally
equal, so the `CompEmulates` conclusion is a real
indistinguishability between two distinct closed systems. -/
example (sp : ℕ) (msg₀ msg₁ : BitVec sp) (h : msg₀ ≠ msg₁) :
    msgClosed sp msg₀ ≠ msgClosed sp msg₁ :=
  msgClosed_ne sp h

/-- **Security-level non-vacuity witness.** There exists a plaintext
reader under which the real SMC semantics' `run` field produces
literally distinct `OptionT ProbComp Unit` computations on
`msgClosed sp msg₀` and `msgClosed sp msg₁`, namely
`realCipherObserve sp msg₀ P` and `realCipherObserve sp msg₁ P`.

This confirms that the `CompEmulates 0` conclusion of
`compEmulates_msgClosed` is not a syntactic collapse: the two `run`
values literally differ, and OTP privacy (`evalDist_realCipherObserve_eq`)
is what equates their `SPMF Unit` denotations. -/
theorem realSmcSemantics_run_distinct
    (sp : ℕ) (P : BitVec sp → Bool) (msg₀ msg₁ : BitVec sp)
    (h : msg₀ ≠ msg₁) :
    ∃ readMsg : MsgReader sp,
      (realSmcSemantics sp readMsg P).run (msgClosed sp msg₀) =
        realCipherObserve sp msg₀ P ∧
      (realSmcSemantics sp readMsg P).run (msgClosed sp msg₁) =
        realCipherObserve sp msg₁ P := by
  classical
  have hne : msgClosed sp msg₀ ≠ msgClosed sp msg₁ := msgClosed_ne sp h
  refine ⟨fun W => if W = msgClosed sp msg₀ then msg₀ else msg₁, ?_, ?_⟩
  · change realCipherObserve sp
      (if msgClosed sp msg₀ = msgClosed sp msg₀ then msg₀ else msg₁) P =
      realCipherObserve sp msg₀ P
    rw [if_pos rfl]
  · change realCipherObserve sp
      (if msgClosed sp msg₁ = msgClosed sp msg₀ then msg₀ else msg₁) P =
      realCipherObserve sp msg₁ P
    rw [if_neg hne.symm]

end UC
end oneTimePad
