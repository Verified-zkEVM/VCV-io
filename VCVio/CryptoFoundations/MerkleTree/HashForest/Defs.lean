/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Hashing.Defs

/-!
# Ordered forests of hash operations

This module models the hash-computation shape shared by root-based Merkle trees, commitment caps,
and constructions whose internal operations consume more than two homogeneous child digests.
Each operation has a caller-chosen kind, context, and address. Its ordered input sequence may mix
local payloads, recursively computed child digests, and public digest constants.

`Payload` is the value visible at the hash-operation boundary, such as encoded bytes or a field
row. Mapping application data into these values belongs to the encoding or logical-layout layer;
the forest does not silently claim that an arbitrary application representation is canonical.

The representation is semantic: it records which digest computations define the public boundary.
It does not prescribe storage layout, proof serialization, or a sparse-opening format. A forest is
an intrinsically sized ordered vector of roots; one root specializes to an ordinary Merkle
commitment, while several roots model a cap without adding a synthetic parent hash.
-/

@[expose] public section

namespace MerkleHashForest

open BinaryTree MerkleTreeHashing OracleComp OracleSpec

universe u v w x y z

/-- One input to a hash operation after its recursive children have been evaluated.

The constructors retain the semantic role of each value. In particular, a public constant is not
silently reclassified as the digest of a child operation. -/
inductive OperationInput (Payload : Type u) (Digest : Type v) (Child : Type w) where
  | payload (value : Payload)
  | child (value : Child)
  | publicConstant (value : Digest)
deriving DecidableEq

/-- A fully evaluated, variadic hash request. -/
structure Query (OperationKind : Type u) (Context : Type v) (Address : Type w)
    (Payload : Type x) (Digest : Type y) where
  /-- Which hash operation or domain is being invoked. -/
  kind : OperationKind
  /-- Public parameters or commitment-instance context for the operation. -/
  context : Context
  /-- Position or tweak address of this operation. -/
  address : Address
  /-- Ordered, role-tagged inputs to the operation. -/
  inputs : List (OperationInput Payload Digest Digest)
deriving DecidableEq

/-- Homogeneous oracle specification for hash-forest operations. -/
@[reducible]
def spec (OperationKind : Type u) (Context : Type v) (Address : Type w)
    (Payload : Type x) (Digest : Type y) :
    OracleSpec (Query OperationKind Context Address Payload Digest) :=
  Query OperationKind Context Address Payload Digest →ₒ Digest

/-- A finite hash-computation tree.

`providedDigest` is an already available digest and performs no query. An `operation` owns one
ordered input list; recursive children occur directly at their input positions, so every stored
child contributes exactly where it appears in the resulting query. -/
inductive Tree (OperationKind : Type u) (Context : Type v) (Address : Type w)
    (Payload : Type x) (Digest : Type y) where
  | providedDigest (value : Digest)
  | operation (kind : OperationKind) (context : Context) (address : Address)
      (inputs : List (OperationInput Payload Digest
        (Tree OperationKind Context Address Payload Digest)))

/-- An ordered public boundary of `rootCount` hash-computation trees. -/
abbrev Forest (OperationKind : Type u) (Context : Type v) (Address : Type w)
    (Payload : Type x) (Digest : Type y) (rootCount : Nat) :=
  List.Vector (Tree OperationKind Context Address Payload Digest) rootCount

variable {OperationKind : Type u} {Context : Type v} {Address : Type w}
  {Payload : Type x} {Digest : Type y}

/-- Expose one computation tree as an ordinary single-root commitment boundary. -/
def Tree.toForest
    (tree : Tree OperationKind Context Address Payload Digest) :
    Forest OperationKind Context Address Payload Digest 1 :=
  ⟨[tree], rfl⟩

namespace Internal

/- The mutually recursive folds below are public only because Lean's module system does not allow
an exposed definition to depend on private implementation declarations. Keep callers on the
documented `evaluateTreeWithHash` and `evaluateTree` entry points. -/
mutual

def evaluateTreeWithHash
    (answer : Query OperationKind Context Address Payload Digest → Digest)
    (tree : Tree OperationKind Context Address Payload Digest) : ULift.{x} Digest := match tree with
  | .providedDigest value => .up value
  | .operation kind context address inputs => .up (answer {
      kind
      context
      address
      inputs := evaluateInputsWithHash answer inputs
    })

def evaluateInputsWithHash
    (answer : Query OperationKind Context Address Payload Digest → Digest) :
    List (OperationInput Payload Digest
      (Tree OperationKind Context Address Payload Digest)) →
      List (OperationInput Payload Digest Digest)
  | [] => []
  | input :: inputs => evaluateInputWithHash answer input :: evaluateInputsWithHash answer inputs

def evaluateInputWithHash
    (answer : Query OperationKind Context Address Payload Digest → Digest) :
    OperationInput Payload Digest (Tree OperationKind Context Address Payload Digest) →
      OperationInput Payload Digest Digest
  | .payload value => .payload value
  | .child tree => .child (evaluateTreeWithHash answer tree).down
  | .publicConstant value => .publicConstant value

end

mutual

def evaluateTree {OperationKind : Type u} {Context : Type v} {Address : Type w}
    {Payload : Type x} {Digest : Type y} {m : Type y → Type z} [Monad m]
    [HasQuery (spec OperationKind Context Address Payload Digest) m]
    (tree : Tree OperationKind Context Address Payload Digest) : m Digest := match tree with
  | .providedDigest value => pure value
  | .operation kind context address inputs => do
      evaluateInputs inputs fun evaluatedInputs =>
        HasQuery.query (spec := spec OperationKind Context Address Payload Digest) {
          kind
          context
          address
          inputs := evaluatedInputs
        }

def evaluateInputs {OperationKind : Type u} {Context : Type v} {Address : Type w}
    {Payload : Type x} {Digest : Type y} {m : Type y → Type z} [Monad m]
    [HasQuery (spec OperationKind Context Address Payload Digest) m] :
    (inputs : List (OperationInput Payload Digest
      (Tree OperationKind Context Address Payload Digest))) →
    (next : List (OperationInput Payload Digest Digest) → m Digest) →
      m Digest
  | [], next => next []
  | input :: inputs, next =>
      evaluateInput input fun evaluatedInput =>
        evaluateInputs inputs fun evaluatedInputs =>
          next (evaluatedInput :: evaluatedInputs)

def evaluateInput {OperationKind : Type u} {Context : Type v} {Address : Type w}
    {Payload : Type x} {Digest : Type y} {m : Type y → Type z} [Monad m]
    [HasQuery (spec OperationKind Context Address Payload Digest) m] :
    (input : OperationInput Payload Digest
      (Tree OperationKind Context Address Payload Digest)) →
    (next : OperationInput Payload Digest Digest → m Digest) →
      m Digest
  | .payload value, next => next (.payload value)
  | .child tree, next => do
      let digest ← evaluateTree tree
      next (.child digest)
  | .publicConstant value, next => next (.publicConstant value)

end

end Internal

/-- Evaluate one hash-computation tree under a deterministic query implementation. -/
def evaluateTreeWithHash
    (answer : Query OperationKind Context Address Payload Digest → Digest)
    (tree : Tree OperationKind Context Address Payload Digest) : Digest :=
  (Internal.evaluateTreeWithHash answer tree).down

/-- Evaluate an ordered forest under a deterministic query implementation. -/
def evaluateForestWithHash {rootCount : Nat}
    (answer : Query OperationKind Context Address Payload Digest → Digest)
    (forest : Forest OperationKind Context Address Payload Digest rootCount) :
    List.Vector Digest rootCount :=
  forest.map (evaluateTreeWithHash answer)

/-- Evaluate one hash-computation tree, querying operations after evaluating their inputs from
left to right.

Only child digests are bound inside the monad; higher-universe payloads are threaded through
continuations without becoming monadic result values. -/
def evaluateTree {OperationKind : Type u} {Context : Type v} {Address : Type w}
    {Payload : Type x} {Digest : Type y} {m : Type y → Type*} [Monad m]
    [HasQuery (spec OperationKind Context Address Payload Digest) m]
    (tree : Tree OperationKind Context Address Payload Digest) : m Digest :=
  Internal.evaluateTree tree

/-- Evaluate the roots of a forest from left to right. -/
def evaluateForest {OperationKind : Type u} {Context : Type v} {Address : Type w}
    {Payload : Type x} {Digest : Type y} {m : Type y → Type*} [Monad m]
    [HasQuery (spec OperationKind Context Address Payload Digest) m] :
    {rootCount : Nat} →
      Forest OperationKind Context Address Payload Digest rootCount →
        m (List.Vector Digest rootCount)
  | 0, _ => pure .nil
  | _ + 1, forest => do
      let root ← evaluateTree forest.head
      let roots ← evaluateForest forest.tail
      pure (.cons root roots)

/-- Replacing the operation oracle by a deterministic implementation gives the pure tree
evaluator. -/
@[simp]
theorem simulateQ_evaluateTree {OperationKind : Type u} {Context : Type v}
    {Address : Type w} {Payload : Type x} {Digest : Type y}
    (answer : QueryImpl (spec OperationKind Context Address Payload Digest) Id)
    (tree : Tree OperationKind Context Address Payload Digest) :
    simulateQ answer
        (evaluateTree
          (m := OracleComp (spec OperationKind Context Address Payload Digest)) tree) =
      evaluateTreeWithHash answer tree := by
  apply Tree.rec
    (motive_1 := fun tree =>
      simulateQ answer
          (Internal.evaluateTree
            (m := OracleComp (spec OperationKind Context Address Payload Digest)) tree) =
        (Internal.evaluateTreeWithHash answer tree).down)
    (motive_2 := fun inputs =>
      ∀ (next : List (OperationInput Payload Digest Digest) →
          OracleComp (spec OperationKind Context Address Payload Digest) Digest)
        (nextWithHash : List (OperationInput Payload Digest Digest) → Digest),
        (∀ evaluatedInputs,
          simulateQ answer (next evaluatedInputs) = nextWithHash evaluatedInputs) →
        simulateQ answer (Internal.evaluateInputs inputs next) =
          nextWithHash (Internal.evaluateInputsWithHash answer inputs))
    (motive_3 := fun input =>
      ∀ (next : OperationInput Payload Digest Digest →
          OracleComp (spec OperationKind Context Address Payload Digest) Digest)
        (nextWithHash : OperationInput Payload Digest Digest → Digest),
        (∀ evaluatedInput,
          simulateQ answer (next evaluatedInput) = nextWithHash evaluatedInput) →
        simulateQ answer (Internal.evaluateInput input next) =
          nextWithHash (Internal.evaluateInputWithHash answer input))
  · intro value
    simp [Internal.evaluateTree, Internal.evaluateTreeWithHash]
    rfl
  · intro kind context address inputs inputsIH
    simp only [Internal.evaluateTree, Internal.evaluateTreeWithHash]
    exact inputsIH
      (fun evaluatedInputs =>
        HasQuery.query (spec := spec OperationKind Context Address Payload Digest) {
          kind, context, address, inputs := evaluatedInputs })
      (fun evaluatedInputs => answer { kind, context, address, inputs := evaluatedInputs })
      (by intro evaluatedInputs; simp)
  · intro next nextWithHash hnext
    simpa [Internal.evaluateInputs, Internal.evaluateInputsWithHash] using hnext []
  · intro head tail headIH tailIH next nextWithHash hnext
    simp only [Internal.evaluateInputs, Internal.evaluateInputsWithHash]
    apply headIH
      (next := fun evaluatedHead =>
        Internal.evaluateInputs tail fun evaluatedTail =>
          next (evaluatedHead :: evaluatedTail))
      (nextWithHash := fun evaluatedHead =>
        nextWithHash (evaluatedHead :: Internal.evaluateInputsWithHash answer tail))
    intro evaluatedHead
    exact tailIH
      (fun evaluatedTail => next (evaluatedHead :: evaluatedTail))
      (fun evaluatedTail => nextWithHash (evaluatedHead :: evaluatedTail))
      (fun evaluatedTail => hnext (evaluatedHead :: evaluatedTail))
  · intro value next nextWithHash hnext
    simpa [Internal.evaluateInput, Internal.evaluateInputWithHash] using
      hnext (.payload value)
  · intro child childIH next nextWithHash hnext
    simp only [Internal.evaluateInput, simulateQ_bind, Internal.evaluateInputWithHash]
    rw [childIH]
    exact hnext _
  · intro value next nextWithHash hnext
    simpa [Internal.evaluateInput, Internal.evaluateInputWithHash] using
      hnext (.publicConstant value)

/-- Deterministic oracle simulation also agrees on every ordered commitment cap. -/
@[simp]
theorem simulateQ_evaluateForest {OperationKind : Type u} {Context : Type v}
    {Address : Type w} {Payload : Type x} {Digest : Type y} {rootCount : Nat}
    (answer : QueryImpl (spec OperationKind Context Address Payload Digest) Id)
    (forest : Forest OperationKind Context Address Payload Digest rootCount) :
    simulateQ answer
        (evaluateForest
          (m := OracleComp (spec OperationKind Context Address Payload Digest)) forest) =
      evaluateForestWithHash answer forest := by
  induction forest using List.Vector.inductionOn with
  | nil => rfl
  | cons rootsIH =>
      simp only [evaluateForest, simulateQ_bind, simulateQ_evaluateTree,
        evaluateForestWithHash, List.Vector.map_cons, List.Vector.head_cons,
        List.Vector.tail_cons, simulateQ_pure]
      rw [rootsIH]
      rfl

end MerkleHashForest
