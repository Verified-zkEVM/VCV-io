/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import Examples.OneTimePad.Basic
import VCVio.Interaction.UC.Computational
import VCVio.Interaction.UC.OpenProcessModel
import VCVio.Interaction.UC.Runtime
import VCVio.OracleComp.Constructions.BitVec

/-!
# One-Time Pad at the UC Observation Layer

This file wires the one-time pad from `Examples.OneTimePad.Basic` into
the `Interaction.UC.Semantics` observation framework, giving a
`CompEmulates 0` statement at the observation level.

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

## Open-world layer: three-port boundary `Δ_otp`

The second half of this file constructs an open UC-style model of
the OTP at a three-port boundary

```
Δ_otp sp = ⟨ keyIn +ᵢ plaintextIn , ctxtOut ⟩
```

where each port carries a `BitVec sp` message. Two structurally
distinct open processes live at this boundary:

* `realOtp sp msg`. Samples a uniform key `k ← BitVec sp` and emits
  the ciphertext `k ⊕ msg` on the `ctxtOut` port via
  `BoundaryAction.emit`.
* `idealOtp sp`. Samples a uniform ciphertext `c ← BitVec sp`
  directly and emits it verbatim on the `ctxtOut` port, ignoring the
  plaintext entirely.

Both processes thread a uniform sampler by lifting `Sampler.uniformI`
from `ProbComp` to `OptionT ProbComp` through `Decoration.map`. They
are structurally distinct whenever `msg ≠ 0` (`realOtp_ne_idealOtp`):
their single-step boundary emissions disagree on the zero key. The
indistinguishability statement `compEmulates_realOtp` follows from
`compEmulates_realSmcSemantics`, which closes over every pair of open
processes at every boundary.

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

The `OptionT ProbComp` target lets `guard` contribute genuine failure
mass to the resulting `SPMF Unit`. -/
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
    𝒟[realCipherObserve sp msg P] =
      𝒟[idealCipherObserve sp P] := by
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
to a plaintext choice. -/
noncomputable def msgClosed (sp : ℕ) (msg : BitVec sp) :
    T.Closed where
  Proc := BitVec sp
  step := fun _ =>
    { spec := .done
      semantics := ⟨⟩
      next := fun _ => msg }
  stepSampler := fun _ => ⟨⟩

/-- Distinct plaintexts give distinct closed processes: the two
processes share the state type `BitVec sp` and the `.done` spec and
differ only in what `step.next` returns on the unit transcript. -/
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

The `run` field depends on the closed-system argument through
`readMsg`; OTP privacy collapses the resulting `SPMF Unit`
denotations into the plaintext-independent ideal one. -/
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
  change 𝒟[realCipherObserve sp (readMsg W) P] =
      𝒟[idealCipherObserve sp P]
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
      (𝒟[idealCipherObserve sp P])
      (𝒟[idealCipherObserve sp P]) ≤ 0
  simp [SPMF.tvDist_self]

/-! ## Concrete instantiation: two structurally distinct closed systems -/

/-- **Plaintext indistinguishability from OTP privacy.** For any two
plaintexts `msg₀`, `msg₁` and any distinguisher predicate `P`, the
closed systems `msgClosed sp msg₀` and `msgClosed sp msg₁` are
indistinguishable under the real SMC semantics. When `msg₀ ≠ msg₁`
the two closed systems are themselves distinct (`msgClosed_ne`), so
the indistinguishability comes from OTP privacy rather than from
`W_real = W_ideal`. -/
theorem compEmulates_msgClosed (sp : ℕ) (readMsg : MsgReader sp)
    (P : BitVec sp → Bool) (msg₀ msg₁ : BitVec sp) :
    CompEmulates (realSmcSemantics sp readMsg P) 0
      (msgClosed sp msg₀) (msgClosed sp msg₁) :=
  compEmulates_realSmcSemantics sp readMsg P
    (msgClosed sp msg₀) (msgClosed sp msg₁)

/-- There is a plaintext reader under which `realSmcSemantics.run`
produces distinct `OptionT ProbComp Unit` computations on
`msgClosed sp msg₀` and `msgClosed sp msg₁`, namely
`realCipherObserve sp msg₀ P` and `realCipherObserve sp msg₁ P`.
OTP privacy (`evalDist_realCipherObserve_eq`) is what equates their
`SPMF Unit` denotations despite the distinct `run` values. -/
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

/-! ## Open-world layer: three-port boundary `Δ_otp` -/

/-- The single-port input interface carrying a `BitVec sp` message.
Used both for the key-input port (from the KDC) and the
plaintext-input port (from the sender). -/
def bvInInterface (sp : ℕ) : Interface where
  A := Unit
  B := fun _ => BitVec sp

/-- The single-port output interface carrying a `BitVec sp` message,
used for the ciphertext-output port. -/
def bvOutInterface (sp : ℕ) : Interface where
  A := Unit
  B := fun _ => BitVec sp

/-- The three-port open boundary for the UC-level OTP:
inputs are the disjoint sum of a key port and a plaintext port, each
carrying a `BitVec sp` message; outputs are a single ciphertext port
carrying a `BitVec sp` message. -/
def Δ_otp (sp : ℕ) : PortBoundary where
  In := Interface.sum (bvInInterface sp) (bvInInterface sp)
  Out := bvOutInterface sp

/-- The single-round interaction spec at the core of both real and
ideal OTP processes: one node samples a `BitVec sp` (the key for the
real world, the ciphertext for the ideal world), then terminates. -/
abbrev otpSpec (sp : ℕ) : Interaction.Spec.{0} :=
  Spec.node (BitVec sp) (fun _ => Spec.done)

/-- The canonical uniform `ProbComp`-sampler for `otpSpec sp`,
synthesized from the `Spec.Fintype (otpSpec sp)` instance built by
typeclass synthesis from `Fintype (BitVec sp)` and
`Nonempty (BitVec sp)`. -/
noncomputable def uniformOtpSampler (sp : ℕ) :
    Spec.Sampler ProbComp (otpSpec sp) :=
  Spec.Sampler.uniformI _

/-- Lift a `ProbComp`-valued sampler to an `OptionT ProbComp`-valued
one by applying `liftM : ProbComp X → OptionT ProbComp X` at every
node of the spec tree via `Decoration.map`.

This is how we thread a real uniform sampler through an open process
whose surface monad is `OptionT ProbComp` (the observation monad used
by the bundled `UC.Semantics` above). -/
noncomputable def liftSamplerToOptionT {spec : Interaction.Spec.{0}}
    (s : Spec.Sampler ProbComp spec) :
    Spec.Sampler (OptionT ProbComp) spec :=
  Spec.Decoration.map
    (Γ := fun X => ProbComp X) (Δ := fun X => OptionT ProbComp X)
    (fun _ (x : ProbComp _) => (liftM x : OptionT ProbComp _)) spec s

/-- The uniform `OptionT ProbComp`-sampler for `otpSpec sp`, obtained
by lifting `uniformOtpSampler`. Both `realOtp` and `idealOtp` thread
this same sampler, so their distributional content lives in the
boundary emission, not in the sampler. -/
noncomputable def otpStepSampler (sp : ℕ) :
    Spec.Sampler (OptionT ProbComp) (otpSpec sp) :=
  liftSamplerToOptionT (uniformOtpSampler sp)

/-! ### Boundary emissions: real vs ideal -/

/-- Real-world boundary emission. On the unique sample node of
`otpSpec sp`, when the sampler produces `k : BitVec sp`, emit one
packet on the single output port of `Δ_otp sp` carrying the
ciphertext `k ⊕ msg`. -/
def realEmit (sp : ℕ) (msg : BitVec sp) :
    PFunctor.Trace (Δ_otp sp).Out (BitVec sp) :=
  fun k => [⟨(), k ^^^ msg⟩]

/-- Ideal-world boundary emission. On the unique sample node of
`otpSpec sp`, when the sampler produces `c : BitVec sp`, emit it
verbatim on the single output port of `Δ_otp sp`.

Under the uniform sampler this is already the correct distribution
on ciphertexts, so no plaintext input is needed: the ideal
functionality's simulator is realised directly by the emission
structure. -/
def idealEmit (sp : ℕ) :
    PFunctor.Trace (Δ_otp sp).Out (BitVec sp) :=
  fun c => [⟨(), c⟩]

/-- The open-node context at the unique sample node of `otpSpec sp`:
trivial controllers and views, and the given boundary emission
action. -/
def otpOpenNode (sp : ℕ)
    (emit : PFunctor.Trace (Δ_otp sp).Out (BitVec sp)) :
    UC.OpenNodeContext Party (Δ_otp sp) (BitVec sp) where
  toNodeProfile :=
    { controllers := fun _ => []
      views := fun _ => .hidden }
  boundary :=
    { isActivated := false
      emit := emit }

/-- Decoration for `otpSpec sp` bundling a single `otpOpenNode` at the
root and the trivial `PUnit` decoration at the terminal leaf. -/
def otpDecoration (sp : ℕ)
    (emit : PFunctor.Trace (Δ_otp sp).Out (BitVec sp)) :
    Spec.Decoration (UC.OpenNodeContext Party (Δ_otp sp)) (otpSpec sp) :=
  ⟨otpOpenNode sp emit, fun _ => ⟨⟩⟩

/-! ### Real and ideal open processes -/

/-- **Real-world OTP open process** at `Δ_otp sp`.

State space `Unit` (single-round, one-shot). Every step runs the
single-sample `otpSpec sp`, emitting the ciphertext `k ⊕ msg` on the
output port via `realEmit`, with the uniform sampler threaded through
`otpStepSampler`. -/
noncomputable def realOtp (sp : ℕ) (msg : BitVec sp) :
    T.Obj (Δ_otp sp) where
  Proc := Unit
  step := fun _ =>
    { spec := otpSpec sp
      semantics := otpDecoration sp (realEmit sp msg)
      next := fun _ => () }
  stepSampler := fun _ => otpStepSampler sp

/-- **Ideal-world OTP open process** at `Δ_otp sp`.

State space `Unit`. Every step samples a uniform ciphertext
`c ← BitVec sp` and emits `c` on the output port via `idealEmit`.
The plaintext input is never consulted: the simulator is realised
directly by the emission.

Distributional equivalence with `realOtp` is a theorem, not a
structural identity: OTP privacy (`evalDist_realCipherObserve_eq`)
collapses the two bundled `SPMF Unit` observations. -/
noncomputable def idealOtp (sp : ℕ) : T.Obj (Δ_otp sp) where
  Proc := Unit
  step := fun _ =>
    { spec := otpSpec sp
      semantics := otpDecoration sp (idealEmit sp)
      next := fun _ => () }
  stepSampler := fun _ => otpStepSampler sp

/-! ### Structural distinctness -/

/-- For any nonzero plaintext `msg`, the real and ideal OTP open
processes at `Δ_otp sp` are not equal: they agree on `Proc`,
`step.spec`, `step.next`, and `stepSampler`, but their
`step.semantics`'s boundary emissions disagree on the all-zero key
(`0#sp ^^^ msg = msg ≠ 0#sp`). -/
theorem realOtp_ne_idealOtp (sp : ℕ) {msg : BitVec sp}
    (hmsg : msg ≠ 0#sp) :
    realOtp sp msg ≠ idealOtp sp := by
  intro heq
  apply hmsg
  have hstep : HEq (realOtp sp msg).step (idealOtp sp).step := by rw [heq]
  have hstep' : (realOtp sp msg).step = (idealOtp sp).step :=
    eq_of_heq hstep
  have hstep0 := congrFun hstep' ()
  change
    ({ spec := otpSpec sp,
       semantics := otpDecoration sp (realEmit sp msg),
       next := fun _ => () } :
      Concurrent.StepOver (UC.OpenNodeContext Party (Δ_otp sp)) Unit) =
    { spec := otpSpec sp,
      semantics := otpDecoration sp (idealEmit sp),
      next := fun _ => () } at hstep0
  injection hstep0 with _ hsem _
  have hemit : realEmit sp msg = idealEmit sp := by
    have := congrArg (·.1.boundary.emit) hsem
    exact this
  have h0 := congrFun hemit (0#sp)
  change [(⟨(), 0#sp ^^^ msg⟩ : Σ _ : Unit, BitVec sp)] =
      [(⟨(), 0#sp⟩ : Σ _ : Unit, BitVec sp)] at h0
  simp only [List.cons.injEq, Sigma.mk.injEq, and_true,
    BitVec.zero_xor, heq_eq_eq] at h0
  exact h0.2

/-! ### UC indistinguishability at the open-world boundary -/

/-- **OTP UC indistinguishability at `Δ_otp sp`.**

For every plaintext reader and distinguisher predicate, the real and
ideal OTP open processes at the three-port boundary `Δ_otp sp` are
`CompEmulates 0`-indistinguishable under `realSmcSemantics`.

Since `compEmulates_realSmcSemantics` quantifies over every pair of
open processes at every boundary, this follows directly. The content
lives one level down: OTP privacy
(`evalDist_realCipherObserve_eq`) collapses the real and ideal
bundled observations into the same `SPMF Unit`, regardless of what
open-world object is plugged into the closed system. -/
theorem compEmulates_realOtp (sp : ℕ) (msg : BitVec sp)
    (readMsg : MsgReader sp) (P : BitVec sp → Bool) :
    CompEmulates (realSmcSemantics sp readMsg P) 0
      (realOtp sp msg) (idealOtp sp) :=
  compEmulates_realSmcSemantics sp readMsg P (realOtp sp msg) (idealOtp sp)

end UC
end oneTimePad
