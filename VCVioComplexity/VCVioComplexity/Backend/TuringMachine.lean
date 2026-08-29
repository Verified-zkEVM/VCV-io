/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexitylib.Models.TuringMachine
public import Mathlib.Data.BitVec
public import Mathlib.Data.List.OfFn
public import PolyFun.Realizability.Quantitative.Closure
public import PolyFun.Realizability.Representation
public import VCVioComplexity.Asymptotics.PolyBound

/-!
# Exact complexitylib machine certificates

This module gives an inspectable, Type-valued backend certificate for functions between explicit
PolyFun word representations. A certificate contains one concrete complexitylib Turing machine,
its total function on words, and an exact terminating run on every word. Its semantic correctness
field relates that total word function to the represented Lean function only on valid encodings.

The exact run length is the local work measure intended for PolyFun quantitative realizations.
`quantitativeStepClass` is already inhabited by individual exact codes. General identity and
composition remain obligations of PolyFun's optional category and exact-category mixins. No such
closure instance is claimed here: the pinned complexitylib revision's composition and Hoare
modules do not compile with VCVio's Lean toolchain.

This file therefore establishes a concrete deterministic step-function backend, not an oracle-TM
adequacy theorem and not an unqualified notion of probabilistic polynomial time.
-/

@[expose] public section

namespace VCVioComplexity.Backend.TuringMachine

/-- Binary words used by the pinned complexitylib machine model. -/
abbrev Word := List Bool

namespace WordCodec

/-! ## Primitive value codecs -/

/-- Unary security-parameter encoding. The word consists of exactly `n` one bits. -/
def unaryNatEncode (n : ℕ) : Word :=
  List.replicate n true

/-- Partial unary decoder, rejecting any word containing a zero bit. -/
def unaryNatDecode (word : Word) : Option ℕ :=
  if word.all id then some word.length else none

@[simp]
theorem unaryNatDecode_encode (n : ℕ) : unaryNatDecode (unaryNatEncode n) = some n := by
  simp [unaryNatDecode, unaryNatEncode]

/-- Canonical unary retraction used for a cryptographic security parameter. -/
def unaryNat : PFunctor.StepClass.CodeRetract Word ℕ where
  encode := unaryNatEncode
  decode := unaryNatDecode
  decode_encode := unaryNatDecode_encode

/-- Little-endian, fixed-width encoding of a `BitVec` with no length prefix. -/
def fixedBitVecEncode {width : ℕ} (value : BitVec width) : Word :=
  List.ofFn value.getLsb

/-- Partial fixed-width decoder. Words of the wrong width are rejected. -/
def fixedBitVecDecode (width : ℕ) (word : Word) : Option (BitVec width) :=
  if word.length = width then some ((BitVec.ofBoolListLE word).setWidth width) else none

@[simp]
theorem fixedBitVecDecode_encode {width : ℕ} (value : BitVec width) :
    fixedBitVecDecode width (fixedBitVecEncode value) = some value := by
  simp only [fixedBitVecDecode, fixedBitVecEncode, List.length_ofFn, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD, hindex]

/-- Canonical fixed-width bit-vector retraction. -/
def fixedBitVec (width : ℕ) : PFunctor.StepClass.CodeRetract Word (BitVec width) where
  encode := fixedBitVecEncode
  decode := fixedBitVecDecode width
  decode_encode := fixedBitVecDecode_encode

/-- Prefix-free pairing of two binary words.

Each bit of the first word is preceded by `false`; a lone `true` terminates the first component. -/
def pair : Word → Word → Word
  | [], right => true :: right
  | bit :: left, right => false :: bit :: pair left right

/-- Total parser for `pair`; malformed words are sent to the empty pair. -/
def unpair : Word → Word × Word
  | [] => ([], [])
  | true :: rest => ([], rest)
  | [false] => ([], [])
  | false :: bit :: rest =>
      let result := unpair rest
      (bit :: result.1, result.2)

@[simp] theorem unpair_pair (left right : Word) : unpair (pair left right) = (left, right) := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp [pair, unpair, ih]

/-- PolyFun pairing structure induced by `pair` and `unpair`. -/
def pairing : PFunctor.StepClass.CodePairing Word where
  pair := pair
  fst word := (unpair word).1
  snd word := (unpair word).2
  fst_pair left right := by simp
  snd_pair left right := by simp

/-- One-bit tags for binary sums. -/
def sum : PFunctor.StepClass.CodeSum Word where
  inl payload := false :: payload
  inr payload := true :: payload
  split
    | [] => none
    | false :: payload => some (Sum.inl payload)
    | true :: payload => some (Sum.inr payload)
  split_inl _ := rfl
  split_inr _ := rfl

/-- The empty word represents `none`; a leading `true` represents `some`. -/
def option : PFunctor.StepClass.CodeOption Word where
  noneCode := []
  someCode payload := true :: payload
  split
    | [] => some none
    | true :: payload => some (some payload)
    | false :: _ => none
  split_none := rfl
  split_some _ := rfl

end WordCodec

/-- Trusted syntax of semantic binary-word representations.

Only the listed constructors are available. In particular, clients cannot install an arbitrary
equivalence whose encoder hides noncomputable advice. More base constructors can be added together
with explicit codecs as the concrete backend grows. -/
inductive Representation : Type → Type 1 where
  /-- Binary words represent themselves. -/
  | word : Representation Word
  /-- The unit type has its canonical empty-word representation. -/
  | unit : Representation PUnit
  /-- Booleans have their canonical one-bit representation. -/
  | bool : Representation Bool
  /-- Natural numbers used as security parameters have their canonical unary representation. -/
  | natUnary : Representation ℕ
  /-- Fixed-width bit vectors are packed little-endian without a length prefix. -/
  | bitVec (width : ℕ) : Representation (BitVec width)
  /-- Any empty carrier has the unique vacuous encoding.

  The constructor requires an eliminator into `PEmpty`; it cannot represent an inhabited type or
  cache information because there is no value on which its encoder can run. -/
  | empty {A : Type} (eliminate : A → PEmpty.{0}) : Representation A
  /-- Structural product representation. -/
  | prod {A B : Type} : Representation A → Representation B → Representation (A × B)
  /-- Structural dependent-pair representation.

  This is the native shape of a polynomial-functor position together with one response selected
  by that position.  Keeping it in the trusted syntax lets oracle boundaries be represented
  without admitting arbitrary semantic encoders. -/
  | sigma {I : Type} {A : I → Type} :
      Representation I → (∀ i, Representation (A i)) → Representation (Σ i, A i)
  /-- Structural sum representation. -/
  | sum {A B : Type} : Representation A → Representation B → Representation (A ⊕ B)
  /-- Structural optional-value representation. -/
  | option {A : Type} : Representation A → Representation (Option A)

namespace Representation

/-- Interpret trusted representation syntax as a semantic word retraction. -/
def toCodeRetract {A : Type} : Representation A → PFunctor.StepClass.CodeRetract Word A
  | .word => PFunctor.StepClass.CodeRetract.id Word
  | .unit =>
      { encode := fun _ ↦ []
        decode := fun word ↦ if word = [] then some PUnit.unit else none
        decode_encode := fun _ ↦ rfl }
  | .bool =>
      { encode := fun bit ↦ [bit]
        decode := fun
          | [bit] => some bit
          | _ => none
        decode_encode := fun _ ↦ rfl }
  | .natUnary => WordCodec.unaryNat
  | .bitVec width => WordCodec.fixedBitVec width
  | .empty eliminate =>
      { encode := fun value ↦ (eliminate value).elim
        decode := fun _ ↦ none
        decode_encode := fun value ↦ (eliminate value).elim }
  | .prod left right =>
      PFunctor.StepClass.CodeRetract.prod WordCodec.pairing left.toCodeRetract
        right.toCodeRetract
  | .sigma index value =>
      PFunctor.StepClass.CodeRetract.sigma WordCodec.pairing index.toCodeRetract
        (fun i ↦ (value i).toCodeRetract)
  | .sum left right =>
      PFunctor.StepClass.CodeRetract.sum WordCodec.sum left.toCodeRetract right.toCodeRetract
  | .option payload =>
      PFunctor.StepClass.CodeRetract.option WordCodec.option payload.toCodeRetract

/-- Encode a value according to trusted representation syntax. -/
abbrev encode {A : Type} (rep : Representation A) : A → Word :=
  rep.toCodeRetract.encode

/-- Partially decode a word according to trusted representation syntax. -/
abbrev decode {A : Type} (rep : Representation A) : Word → Option A :=
  rep.toCodeRetract.decode

/-- Decoding is a left inverse of encoding. -/
theorem decode_encode {A : Type} (rep : Representation A) (value : A) :
    rep.decode (rep.encode value) = some value :=
  rep.toCodeRetract.decode_encode value

@[simp]
theorem encode_word (word : Word) : Representation.word.encode word = word :=
  rfl

@[simp]
theorem encode_unit (value : PUnit) : Representation.unit.encode value = [] := by
  cases value
  rfl

@[simp]
theorem encode_bool (value : Bool) : Representation.bool.encode value = [value] :=
  rfl

@[simp]
theorem encode_natUnary (value : ℕ) :
    Representation.natUnary.encode value = WordCodec.unaryNatEncode value :=
  rfl

@[simp]
theorem encode_bitVec {width : ℕ} (value : BitVec width) :
    (Representation.bitVec width).encode value = WordCodec.fixedBitVecEncode value :=
  rfl

@[simp]
theorem encode_prod {A B : Type} (left : Representation A) (right : Representation B)
    (value : A × B) :
    (Representation.prod left right).encode value =
      WordCodec.pair (left.encode value.1) (right.encode value.2) :=
  rfl

@[simp]
theorem encode_sigma {I : Type} {A : I → Type} (index : Representation I)
    (value : ∀ i, Representation (A i)) (entry : Σ i, A i) :
    (Representation.sigma index value).encode entry =
      WordCodec.pair (index.encode entry.1) ((value entry.1).encode entry.2) :=
  rfl

@[simp]
theorem encode_sum_inl {A B : Type} (left : Representation A) (right : Representation B)
    (value : A) :
    (Representation.sum left right).encode (Sum.inl value) = false :: left.encode value :=
  rfl

@[simp]
theorem encode_sum_inr {A B : Type} (left : Representation A) (right : Representation B)
    (value : B) :
    (Representation.sum left right).encode (Sum.inr value) = true :: right.encode value :=
  rfl

@[simp]
theorem encode_option_none {A : Type} (payload : Representation A) :
    (Representation.option payload).encode none = [] :=
  rfl

@[simp]
theorem encode_option_some {A : Type} (payload : Representation A) (value : A) :
    (Representation.option payload).encode (some value) = true :: payload.encode value :=
  rfl

end Representation

/-- The encoded length of a represented value. -/
def encodedSize {A : Type} (rep : Representation A) (value : A) : ℕ :=
  (rep.encode value).length

@[simp]
theorem encodedSize_word (word : Word) : encodedSize .word word = word.length :=
  rfl

@[simp]
theorem encodedSize_unit (value : PUnit) : encodedSize .unit value = 0 := by
  cases value
  rfl

@[simp]
theorem encodedSize_bool (value : Bool) : encodedSize .bool value = 1 :=
  rfl

@[simp]
theorem encodedSize_natUnary (value : ℕ) : encodedSize .natUnary value = value := by
  simp [encodedSize, WordCodec.unaryNatEncode]

@[simp]
theorem encodedSize_bitVec {width : ℕ} (value : BitVec width) :
    encodedSize (.bitVec width) value = width := by
  simp [encodedSize, WordCodec.fixedBitVecEncode]

@[simp]
theorem encodedSize_prod {A B : Type} (left : Representation A)
    (right : Representation B) (value : A × B) :
    encodedSize (.prod left right) value =
      (WordCodec.pair (left.encode value.1) (right.encode value.2)).length :=
  rfl

@[simp]
theorem encodedSize_sigma {I : Type} {A : I → Type} (index : Representation I)
    (value : ∀ i, Representation (A i)) (entry : Σ i, A i) :
    encodedSize (.sigma index value) entry =
      (WordCodec.pair (index.encode entry.1) ((value entry.1).encode entry.2)).length :=
  rfl

@[simp]
theorem encodedSize_sum_inl {A B : Type} (left : Representation A)
    (right : Representation B) (value : A) :
    encodedSize (.sum left right) (Sum.inl value) = (left.encode value).length + 1 := by
  simp [encodedSize]

@[simp]
theorem encodedSize_sum_inr {A B : Type} (left : Representation A)
    (right : Representation B) (value : B) :
    encodedSize (.sum left right) (Sum.inr value) = (right.encode value).length + 1 := by
  simp [encodedSize]

@[simp]
theorem encodedSize_option_none {A : Type} (payload : Representation A) :
    encodedSize (.option payload) none = 0 :=
  rfl

@[simp]
theorem encodedSize_option_some {A : Type} (payload : Representation A) (value : A) :
    encodedSize (.option payload) (some value) = (payload.encode value).length + 1 := by
  simp [encodedSize]

/-- One exact terminating run of a deterministic complexitylib Turing machine.

The witness uses `TM.reachesIn`, so `steps` counts actual transitions rather than fuel supplied to
an evaluator. `output_correct` uses complexitylib's delimited output-tape predicate. -/
structure ExactRun {workTapes : ℕ} (machine : Complexity.TM workTapes)
    (input output : Word) where
  /-- The reached halting configuration. -/
  final : Complexity.Cfg workTapes machine.Q
  /-- The exact number of transitions in this witnessed run. -/
  steps : ℕ
  /-- The machine reaches `final` in exactly `steps` transitions. -/
  reaches : machine.reachesIn steps (machine.initCfg input) final
  /-- The witnessed final configuration is halted. -/
  halted : machine.halted final
  /-- The output tape contains the specified delimited binary word. -/
  output_correct : final.output.HasOutput output

namespace ExactRun

variable {workTapes : ℕ} {machine : Complexity.TM workTapes} {input output : Word}

/-- Change only the propositionally equal output word of an exact run. -/
def castOutput {output' : Word} (run : ExactRun machine input output)
    (h : output = output') : ExactRun machine input output' :=
  h ▸ run

/-- Forget exactness and expose the existential witness used by `TM.ComputesInTime`. -/
theorem exists_run (run : ExactRun machine input output) :
    ∃ final steps, machine.reachesIn steps (machine.initCfg input) final ∧
      machine.halted final ∧ final.output.HasOutput output :=
  ⟨run.final, run.steps, run.reaches, run.halted, run.output_correct⟩

end ExactRun

/-- A concrete machine certificate for a represented function.

`wordFunction` is total and `run` covers every binary word, including invalid encodings. The
`encode_eq` law pins its behavior on represented values. This separation avoids silently assuming
that every word is a valid encoding while still matching complexitylib's total word-function API. -/
structure Code {A B : Type} (input : Representation A) (output : Representation B)
    (function : A → B) where
  /-- Number of work tapes used by the concrete machine. -/
  workTapes : ℕ
  /-- The concrete deterministic complexitylib machine. -/
  machine : Complexity.TM workTapes
  /-- The total word function computed by `machine`. -/
  wordFunction : Word → Word
  /-- An exact terminating run on every word. -/
  run : ∀ word, ExactRun machine word (wordFunction word)
  /-- Correctness on the image of the pinned input encoding. -/
  encode_eq : ∀ value, wordFunction (input.encode value) = output.encode (function value)

namespace Code

variable {A B D : Type} {input : Representation A} {middle : Representation B}
  {output : Representation D} {function : A → B} {next : B → D}

/-- Exact transition count on a word. -/
def wordCost (code : Code input middle function) (word : Word) : ℕ :=
  (code.run word).steps

/-- Exact transition count on a represented value. -/
def valueCost (code : Code input middle function) (value : A) : ℕ :=
  code.wordCost (input.encode value)

/-- The certified run specialized to a represented input and semantic output. -/
def semanticRun (code : Code input middle function) (value : A) :
    ExactRun code.machine (input.encode value) (middle.encode (function value)) :=
  (code.run (input.encode value)).castOutput (code.encode_eq value)

/-- Select an exact run from a standard complexitylib bounded-computation theorem.

The selected data is still certified by `TM.reachesIn`; classical choice selects an existing
halting run but cannot manufacture one. This adapter is useful when a complexitylib theorem is
available without a bespoke `Code` constructor. -/
noncomputable def exactRunOfComputesInTime {workTapes : ℕ}
    (machine : Complexity.TM workTapes) (wordFunction : Word → Word) (bound : ℕ → ℕ)
    (computes : machine.ComputesInTime wordFunction bound) (word : Word) :
    ExactRun machine word (wordFunction word) := by
  let final := Classical.choose (computes word)
  let final_spec := Classical.choose_spec (computes word)
  let steps := Classical.choose final_spec
  let run_spec := Classical.choose_spec final_spec
  exact
    { final := final
      steps := steps
      reaches := run_spec.2.1
      halted := run_spec.2.2.1
      output_correct := run_spec.2.2.2 }

/-- The selected exact run retains the bound proved by `ComputesInTime`. -/
theorem exactRunOfComputesInTime_steps_le {workTapes : ℕ}
    (machine : Complexity.TM workTapes) (wordFunction : Word → Word) (bound : ℕ → ℕ)
    (computes : machine.ComputesInTime wordFunction bound) (word : Word) :
    (exactRunOfComputesInTime machine wordFunction bound computes word).steps ≤ bound word.length :=
  (Classical.choose_spec (Classical.choose_spec (computes word))).1

/-- Build a represented code certificate from a standard total word-machine theorem. -/
noncomputable def ofComputesInTime {workTapes : ℕ}
    (machine : Complexity.TM workTapes) (wordFunction : Word → Word) (bound : ℕ → ℕ)
    (computes : machine.ComputesInTime wordFunction bound)
    (encode_eq : ∀ value, wordFunction (input.encode value) = middle.encode (function value)) :
    Code input middle function where
  workTapes := workTapes
  machine := machine
  wordFunction := wordFunction
  run := exactRunOfComputesInTime machine wordFunction bound computes
  encode_eq := encode_eq

/-- Change only the propositionally equal represented function indexed by a code certificate. -/
def castFunction {function' : A → B} (code : Code input middle function)
    (h : function = function') : Code input middle function' :=
  h ▸ code

/-- A worst-case word-length bound for the exact transition count. -/
def RunsWithin (code : Code input middle function) (bound : ℕ → ℕ) : Prop :=
  ∀ word, code.wordCost word ≤ bound word.length

/-- A certified worst-case bound gives complexitylib's standard time-computation predicate. -/
theorem computesInTime (code : Code input middle function) {bound : ℕ → ℕ}
    (hbound : code.RunsWithin bound) :
    code.machine.ComputesInTime code.wordFunction bound := by
  intro word
  let run := code.run word
  exact ⟨run.final, run.steps, hbound word, run.reaches, run.halted, run.output_correct⟩

/-- Polynomial domination of a concrete machine's exact worst-case transition count.

This is deliberately named as a certificate on one code, rather than as `IsPPT` on a semantic
function or oracle computation. -/
structure PolynomialRunCertificate (code : Code input middle function) where
  /-- The chosen worst-case time bound. -/
  bound : ℕ → ℕ
  /-- The concrete natural polynomial dominating the chosen bound. -/
  polynomial : Polynomial ℕ
  /-- The chosen bound is pointwise dominated by the stored polynomial. -/
  bound_le_polynomial : ∀ inputLength, bound inputLength ≤ polynomial.eval inputLength
  /-- Every exact run fits the bound at its word length. -/
  runsWithin : code.RunsWithin bound

namespace PolynomialRunCertificate

/-- Recover the standard complexitylib computation theorem certified by a polynomial run bound. -/
theorem computesInTime {code : Code input middle function}
    (certificate : PolynomialRunCertificate code) :
    code.machine.ComputesInTime code.wordFunction certificate.bound :=
  code.computesInTime certificate.runsWithin

end PolynomialRunCertificate

end Code

/-! ## Polynomial code bundles -/

/-- A concrete exact machine together with a worst-case polynomial run certificate.

Bundling the two objects keeps primitive registration ergonomic while retaining the exact
`TM.reachesIn` run through `code`. The certificate is still a theorem about that same code; this
structure does not replace exact cost by a separately supplied meter. -/
structure PolynomialCode {A B : Type} (input : Representation A) (output : Representation B)
    (function : A → B) where
  /-- The exact total machine certificate. -/
  code : Code input output function
  /-- A polynomial bound on the exact run selected by `code.run`. -/
  certificate : Code.PolynomialRunCertificate code

namespace PolynomialCode

variable {A B : Type} {input : Representation A} {output : Representation B}
  {function : A → B}

/-- Package an exact code and a separately proved polynomial run certificate. -/
def ofCertificate (code : Code input output function)
    (certificate : Code.PolynomialRunCertificate code) :
    PolynomialCode input output function :=
  ⟨code, certificate⟩

/-- Package an exact code using a direct natural-polynomial bound. -/
def ofPolynomial (code : Code input output function) (polynomial : Polynomial ℕ)
    (runsWithin : ∀ word, code.wordCost word ≤ polynomial.eval word.length) :
    PolynomialCode input output function where
  code := code
  certificate :=
    { bound := polynomial.eval
      polynomial := polynomial
      bound_le_polynomial := fun _ ↦ le_rfl
      runsWithin := runsWithin }

/-- Bundle a standard complexitylib computation theorem whose bound is polynomial. -/
noncomputable def ofComputesInTime {workTapes : ℕ}
    (machine : Complexity.TM workTapes) (wordFunction : Word → Word) (bound : ℕ → ℕ)
    (computes : machine.ComputesInTime wordFunction bound) (hPolynomial : PolyBound bound)
    (encode_eq : ∀ value, wordFunction (input.encode value) = output.encode (function value)) :
    PolynomialCode input output function where
  code := Code.ofComputesInTime machine wordFunction bound computes encode_eq
  certificate :=
    { bound := bound
      polynomial := Classical.choose hPolynomial
      bound_le_polynomial := Classical.choose_spec hPolynomial
      runsWithin := fun word ↦
        Code.exactRunOfComputesInTime_steps_le machine wordFunction bound computes word }

/-- Exact transition count on a raw word. -/
abbrev wordCost (code : PolynomialCode input output function) : Word → ℕ :=
  code.code.wordCost

/-- Exact transition count on a represented input. -/
abbrev valueCost (code : PolynomialCode input output function) : A → ℕ :=
  code.code.valueCost

/-- The certified worst-case running-time bound. -/
abbrev bound (code : PolynomialCode input output function) : ℕ → ℕ :=
  code.certificate.bound

/-- The exact run specialized to a represented input and semantic output. -/
abbrev semanticRun (code : PolynomialCode input output function) (value : A) :=
  code.code.semanticRun value

/-- The bundled bound is pointwise dominated by a natural polynomial. -/
theorem bound_isPolynomial (code : PolynomialCode input output function) :
    PolyBound code.bound :=
  ⟨code.certificate.polynomial, code.certificate.bound_le_polynomial⟩

/-- Exact cost on every word is below the bundled worst-case bound. -/
theorem wordCost_le_bound (code : PolynomialCode input output function) (word : Word) :
    code.wordCost word ≤ code.bound word.length :=
  code.certificate.runsWithin word

/-- Exact cost on a semantic input is bounded at its pinned encoded size. -/
theorem valueCost_le_bound (code : PolynomialCode input output function) (value : A) :
    code.valueCost value ≤ code.bound (encodedSize input value) :=
  code.certificate.runsWithin (input.encode value)

/-- Recover complexitylib's standard bounded computation theorem. -/
theorem computesInTime (code : PolynomialCode input output function) :
    code.code.machine.ComputesInTime code.code.wordFunction code.certificate.bound :=
  code.certificate.computesInTime

/-- Change only the propositionally equal semantic function indexed by polynomial code. -/
def castFunction {function' : A → B} (code : PolynomialCode input output function)
    (h : function = function') : PolynomialCode input output function' := by
  cases h
  exact code

end PolynomialCode

/-! ## A concrete base certificate -/

namespace Primitive

/-- A one-sided-tape-safe direction used in an unreachable transition table. -/
def safeDirection (head : Complexity.Γ) : Complexity.Dir3 :=
  if head = Complexity.Γ.start then .right else .stay

/-- A zero-work-tape machine that is already halted and returns the empty word.

Although its transition table is unreachable, it still satisfies complexitylib's structural rule
that a head reading the left-end marker must move right. -/
def haltMachine : Complexity.TM 0 where
  Q := PUnit
  qstart := PUnit.unit
  qhalt := PUnit.unit
  δ := fun _ inputHead _ outputHead =>
    (PUnit.unit, fun index => Fin.elim0 index, .blank, safeDirection inputHead,
      fun index => Fin.elim0 index, safeDirection outputHead)
  δ_right_of_start := by
    intro state inputHead workHeads outputHead
    simp only
    constructor
    · intro h
      simp [safeDirection, h]
    constructor
    · intro index
      exact Fin.elim0 index
    · intro h
      simp [safeDirection, h]

/-- The zero-step run of `haltMachine`. -/
def haltRun (word : Word) : ExactRun haltMachine word [] where
  final := haltMachine.initCfg word
  steps := 0
  reaches := Complexity.TM.reachesIn.zero
  halted := rfl
  output_correct := by simp [Complexity.Tape.HasOutput]

@[simp]
theorem haltRun_steps (word : Word) : (haltRun word).steps = 0 :=
  rfl

/-- Concrete zero-cost code for the constant unit function from any trusted representation. -/
def unitCode {A : Type} (input : Representation A) :
    Code input .unit (fun _ ↦ PUnit.unit) where
  workTapes := 0
  machine := haltMachine
  wordFunction := fun _ ↦ []
  run := haltRun
  encode_eq _ := rfl

/-- The constant-unit code has a pointwise zero polynomial run bound. -/
noncomputable def unitCodePolynomial {A : Type} (input : Representation A) :
    Code.PolynomialRunCertificate (unitCode input) where
  bound := fun _ ↦ 0
  polynomial := Polynomial.C 0
  bound_le_polynomial := fun _ ↦ by simp
  runsWithin := fun _ ↦ Nat.le_refl 0

/-- The constant-unit machine bundled with its zero polynomial certificate. -/
noncomputable def unitPolynomialCode {A : Type} (input : Representation A) :
    PolynomialCode input .unit (fun _ ↦ PUnit.unit) :=
  PolynomialCode.ofCertificate (unitCode input) (unitCodePolynomial input)

/-- The zero-step unit code is an exact polynomial identity on the unit representation. -/
noncomputable def unitIdentityPolynomial : PolynomialCode .unit .unit id :=
  (unitPolynomialCode .unit).castFunction (by
    funext value
    cases value
    rfl)

end Primitive

/-! ## Inhabited exact-code model -/

/-- A qualitative carrier for the trusted representation grammar.

Its morphism predicate is deliberately unrestricted: computational evidence lives in the
Type-valued `quantitativeStepClass.Realizer`, where it must contain an actual complexitylib
machine and exact runs. Consequently this carrier alone makes no complexity claim. Keeping the
qualitative layer broad lets individual exact codes be useful before the backend has proved
machine-level identity and composition. -/
def stepClass : PFunctor.StepClass where
  Str := Representation
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

/-- The structural product representation available at the qualitative carrier layer. -/
@[instance_reducible]
def hasProd : stepClass.HasProd where
  prod := Representation.prod
  fst_mem _ _ := trivial
  snd_mem _ _ := trivial
  pair_mem _ _ := trivial

/-- The structural sum representation available at the qualitative carrier layer. -/
@[instance_reducible]
def hasSum : stepClass.HasSum where
  sum := Representation.sum
  inl_mem _ _ := trivial
  inr_mem _ _ := trivial
  elim_mem _ _ := trivial

/-- The structural optional-value representation available at the qualitative carrier layer. -/
@[instance_reducible]
def hasOption : @PFunctor.StepClass.HasOption stepClass hasProd := by
  letI := hasProd
  exact
    { option := Representation.option
      omap_mem := fun _ ↦ trivial
      none_mem := fun _ _ ↦ trivial
      obindCtx_mem := fun _ ↦ trivial
      some_mem := fun _ ↦ trivial }

/-- Qualitative distributivity of the trusted structural representations. -/
theorem isDistributive : @PFunctor.StepClass.IsDistributive stepClass hasProd hasSum := by
  let _ := hasProd
  let _ := hasSum
  exact ⟨fun _ _ _ ↦ trivial⟩

/-- The inhabited PolyFun quantitative backend of individual exact-machine certificates.

This definition requires neither identity nor composition. Its realizers are the concrete `Code`
objects above, and its cost is definitionally the transition count of their selected exact
`TM.reachesIn` runs. -/
def quantitativeStepClass : PFunctor.QuantitativeStepClass stepClass where
  Realizer input output function := Code input output function
  size := encodedSize
  cost code value := code.valueCost value
  admissible _ := trivial

@[simp]
theorem quantitativeStepClass_size {A : Type} (rep : Representation A) (value : A) :
    quantitativeStepClass.size rep value = encodedSize rep value :=
  rfl

@[simp]
theorem quantitativeStepClass_cost {A B : Type} {input : Representation A}
    {output : Representation B} {function : A → B}
    (code : Code input output function) (value : A) :
    quantitativeStepClass.cost code value = code.valueCost value :=
  rfl

/-- The inhabited sub-backend whose individual realizers additionally carry polynomial bounds.

This still does not assume categorical closure: a single `PolynomialCode` is useful immediately.
General identity and composition evidence is expressed directly by PolyFun's
`QuantitativeStepClass.HasCategory` mixin. -/
def polynomialQuantitativeStepClass : PFunctor.QuantitativeStepClass stepClass where
  Realizer input output function := PolynomialCode input output function
  size := encodedSize
  cost code value := code.valueCost value
  admissible _ := trivial

@[simp]
theorem polynomialQuantitativeStepClass_size {A : Type} (rep : Representation A) (value : A) :
    polynomialQuantitativeStepClass.size rep value = encodedSize rep value :=
  rfl

@[simp]
theorem polynomialQuantitativeStepClass_cost {A B : Type} {input : Representation A}
    {output : Representation B} {function : A → B}
    (code : PolynomialCode input output function) (value : A) :
    polynomialQuantitativeStepClass.cost code value = code.valueCost value :=
  rfl

namespace Primitive

/-- An inhabited polynomial quantitative realizer, exposed as a small end-to-end canary. -/
noncomputable def unitIdentityRealizer :
    polynomialQuantitativeStepClass.Realizer .unit .unit id :=
  unitIdentityPolynomial

@[simp]
theorem unitIdentityRealizer_cost (value : PUnit) :
    polynomialQuantitativeStepClass.cost unitIdentityRealizer value = 0 :=
  rfl

end Primitive

/-! ## Optional closure seam

General machine-level closure is intentionally absent.  A future implementation must inhabit
PolyFun's `QuantitativeStepClass.HasCategory`, `HasExactCategory`, `HasProd`, `HasSum`,
`HasOption`, and `IsDistributive` mixins directly for the step class above.  Keeping one set of
interfaces prevents the adapter from drifting away from the generic composition API. -/

end VCVioComplexity.Backend.TuringMachine
