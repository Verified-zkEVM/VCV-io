/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.HashForest.Binary

/-!
# Canary tests for Merkle hash forests

These examples pin mixed input roles, variable operation arity, ordered cap outputs, depth-first
query order, query-free provided digests, and agreement with the addressed binary Merkle engine.
-/

@[expose] public section

namespace VCVioTest.MerkleHashForestCanary

open BinaryTree MerkleHashForest MerkleTreeHashing

inductive TestOperationKind where
  | leaf
  | mixed
  | wide
deriving DecidableEq

def kindCode : TestOperationKind → Nat
  | .leaf => 0
  | .mixed => 1
  | .wide => 2

def inputCode : OperationInput Nat (List Nat) (List Nat) → List Nat
  | .payload value => [0, value]
  | .child digest => 1 :: digest
  | .publicConstant digest => 2 :: digest

/-- A role- and order-sensitive operation implementation. -/
def answer : Query TestOperationKind Nat Nat Nat (List Nat) → List Nat
  | ⟨kind, context, address, inputs⟩ =>
      [kindCode kind, context, address] ++ inputs.flatMap inputCode

def hashedLeaf : Tree TestOperationKind Nat Nat Nat (List Nat) :=
  .operation .leaf 7 1 [.payload 3]

def hashedLeafRight : Tree TestOperationKind Nat Nat Nat (List Nat) :=
  .operation .leaf 7 2 [.payload 6]

def mixedRoot : Tree TestOperationKind Nat Nat Nat (List Nat) :=
  .operation .mixed 7 8
    [.child hashedLeaf, .payload 4, .publicConstant [5], .child hashedLeafRight]

def wideRoot : Tree TestOperationKind Nat Nat Nat (List Nat) :=
  .operation .wide 7 9
    [.child (.providedDigest [1]), .child (.providedDigest [2]),
      .child (.providedDigest [3])]

def cap : Forest TestOperationKind Nat Nat Nat (List Nat) 2 :=
  .cons mixedRoot (.cons wideRoot .nil)

abbrev Trace := List (Query TestOperationKind Nat Nat Nat (List Nat))

abbrev TraceM (Result : Type) := Trace → Result × Trace

instance instMonadTraceM : Monad TraceM where
  pure result trace := (result, trace)
  bind action next trace :=
    let (result, trace') := action trace
    next result trace'

@[simp]
private theorem tracePure_apply {Result : Type} (result : Result) (trace : Trace) :
    (pure result : TraceM Result) trace = (result, trace) :=
  rfl

@[simp]
private theorem traceBind_apply {Left Right : Type} (action : TraceM Left)
    (next : Left → TraceM Right) (trace : Trace) :
    (action >>= next) trace =
      let (result, trace') := action trace
      next result trace' :=
  rfl

instance instHasQueryTraceM :
    HasQuery (spec TestOperationKind Nat Nat Nat (List Nat)) TraceM where
  query query := fun trace => (answer query, trace ++ [query])

def capRun := evaluateForest (m := TraceM) cap []

/-- A cap exposes both roots in order, with no synthetic parent operation. The first root mixes two
computed child digests, a local payload, and a public constant in one ordered request. -/
example : (evaluateForestWithHash answer cap).toList =
    [[1, 7, 8, 1, 0, 7, 1, 0, 3, 0, 4, 2, 5, 1, 0, 7, 2, 0, 6],
      [2, 7, 9, 1, 1, 1, 2, 1, 3]] := by
  decide

/-- Forest evaluation is depth-first and root-ordered. Provided digests issue no query, and the
parent request contains the evaluated child digest at its original input position. -/
example : (capRun.1.toList, capRun.2) =
    ([[1, 7, 8, 1, 0, 7, 1, 0, 3, 0, 4, 2, 5, 1, 0, 7, 2, 0, 6],
        [2, 7, 9, 1, 1, 1, 2, 1, 3]],
      [
        { kind := .leaf, context := 7, address := 1, inputs := [.payload 3] },
        { kind := .leaf, context := 7, address := 2, inputs := [.payload 6] },
        { kind := .mixed, context := 7, address := 8,
          inputs := [.child [0, 7, 1, 0, 3], .payload 4,
            .publicConstant [5], .child [0, 7, 2, 0, 6]] },
        { kind := .wide, context := 7, address := 9,
          inputs := [.child [1], .child [2], .child [3]] }
      ]) := by
  simp [capRun, cap, mixedRoot, hashedLeaf, hashedLeafRight, wideRoot,
    evaluateForest, evaluateTree, Internal.evaluateTree, Internal.evaluateInputs,
    Internal.evaluateInput, answer, inputCode, kindCode, List.Vector.head_cons,
    List.Vector.tail_cons]

def twoLeaves : Skeleton := .internal .leaf .leaf

def binaryAddressing : Addressing twoLeaves Bool Unit where
  leaf
    | .ofLeft .ofLeaf => false
    | .ofRight .ofLeaf => true
  node
    | .ofInternal => ()

def binaryPayloads : LeafData Nat twoLeaves := .internal (.leaf 3) (.leaf 5)

/-- A total general-operation implementation whose binary fragment distinguishes leaf addresses
and ordered node inputs. -/
def binaryGeneralAnswer :
    Query BinaryOperationKind Unit (BinaryAddress Bool Unit) Nat Nat → Nat
  | ⟨.leaf, (), .leaf false, [.payload input]⟩ => 100 + input
  | ⟨.leaf, (), .leaf true, [.payload input]⟩ => 200 + input
  | ⟨.node, (), .node (), [.child left, .child right]⟩ => 10 * left + right
  | _ => 0

/-- The translated forest computation agrees with the existing addressed binary builder on a
noncommutative two-leaf example. -/
example :
    evaluateTreeWithHash binaryGeneralAnswer
      (binaryTree binaryAddressing (.hash fun payload => payload + 1) binaryPayloads) = 1246 := by
  decide

/-- Operation payloads and output digests remain universe-independent. -/
example {LargePayload : Type 1} (payload : LargePayload) :
    Tree Unit Unit Unit LargePayload Nat :=
  .operation () () () [.payload payload, .publicConstant 0]

/-- The effectful evaluator preserves the same universe separation without storing payloads in
the response-typed monad. -/
example {LargePayload : Type 1} (payload : LargePayload) :
    OracleComp (spec Unit Unit Unit LargePayload Nat) Nat :=
  evaluateTree (.operation () () () [.payload payload, .publicConstant 0])

end VCVioTest.MerkleHashForestCanary
