/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Basic

/-!
# Branch paths and telescopes for `PFunctor.FreeM`

This file contains the path-dependent structure that lives on top of the
basic free monad on a polynomial functor.

For a polynomial/container `P`, `PFunctor.FreeM P α` is the inductive type of
well-founded `P`-branching trees with leaves labelled by `α`. The definitions
below isolate the canonical branch object of such a tree:

* `FreeM.Transcript s` records a complete root-to-leaf branch through `s`.
* `FreeM.output s tr` recovers the leaf payload selected by that branch.
* `FreeM.append s k` grafts a suffix tree selected by the branch path of `s`.
* `FreeM.Telescope` is the state-indexed initial algebra obtained by iterating
  such rounds, where the next state is selected by a branch path.

## Terminology and references

The same object appears under several names in the literature. In polynomial
functor language, the free monad on a polynomial is a type of terminating
decision trees. In container and W-type language, these are well-founded trees
and `Transcript` is the type of paths through such a tree. In dependent-type
presentations of games, these are dependent type trees and paths. In programming
language semantics, the coinductive analogue is an interaction tree.

Relevant references include:

* Hancock and Setzer, *Interactive Programs in Dependent Type Theory*, for
  dependent I/O-trees over command-response worlds.
* Altenkirch, Ghani, Hancock, McBride, and Morris, *Indexed Containers*, for
  containers, indexed containers, and interaction structures.
* Libkind and Spivak, *Pattern runs on matter*, for free polynomial monads as
  terminating decision trees.
* Escardo and Oliva, *Higher-order games with dependent types*, for dependent
  type trees and paths in history-dependent games.
* Xia, Zakowski, He, Hur, Malecha, Pierce, and Zdancewic, *Interaction Trees*,
  for the coinductive programming-language analogue.
-/

@[expose] public section

universe v w z t uA uB

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- A complete branch through a `FreeM` tree. For a terminal `pure` leaf the
branch is trivial; for a `roll a rest` node it consists of a child choice
`b : P.B a` and a branch through the selected subtree `rest b`.

For ordinary interaction specs this is the usual transcript. More generally,
the observed branch data is determined entirely by the polynomial fiber `P.B`;
positions with singleton fibers contribute no nontrivial branch choice. -/
def Transcript {α : Type v} : FreeM P α → Type uB
  | .pure _ => PUnit
  | .roll a rest => (b : P.B a) × Transcript (rest b)

/-- The leaf payload selected by a branch transcript. Although the transcript
itself records only branch choices, the tree and transcript together determine
the terminal `pure` payload. -/
def output : (s : FreeM P α) → Transcript s → α
  | .pure x, _ => x
  | .roll _ rest, ⟨b, tr⟩ => output (rest b) tr

@[simp]
theorem output_pure (x : α) (tr : Transcript (FreeM.pure (P := P) x)) :
    output (FreeM.pure x) tr = x := rfl

@[simp]
theorem output_roll (a : P.A) (rest : P.B a → FreeM P α)
    (b : P.B a) (tr : Transcript (rest b)) :
    output (FreeM.roll a rest) ⟨b, tr⟩ = output (rest b) tr := rfl

/-- Dependent sequential composition for `FreeM` trees. Run `s₁`, then
continue with a suffix selected by the branch transcript of `s₁`; the suffix
may change the leaf payload from `α` to `β`.

The payload produced by `s₁` is still available to the suffix as
`FreeM.output s₁ tr`, since it is determined by the tree and branch transcript. -/
def append {β : Type w} :
    (s₁ : FreeM P α) →
    (Transcript s₁ → FreeM P β) →
    FreeM P β
  | .pure _, s₂ => s₂ ⟨⟩
  | .roll a rest, s₂ =>
      .roll a fun b => append (rest b) (fun p => s₂ ⟨b, p⟩)

@[simp]
theorem append_pure {β : Type w} (x : α)
    (s₂ : Transcript (FreeM.pure (P := P) x) → FreeM P β) :
    append (FreeM.pure x) s₂ = s₂ ⟨⟩ := rfl

@[simp]
theorem append_roll {β : Type w} (a : P.A) (rest : P.B a → FreeM P α)
    (s₂ : Transcript (FreeM.roll a rest) → FreeM P β) :
    append (FreeM.roll a rest) s₂ =
      FreeM.roll a (fun b => append (rest b) (fun p => s₂ ⟨b, p⟩)) := rfl

/-! ## Telescopes -/

/-- Initial-algebra presentation of a state-machine telescope of `FreeM`
rounds. At each state `s`, an inhabitant either terminates or extends by
running `round s` and recursing into the next state selected by the branch
transcript of that round. -/
inductive Telescope {St : Type z} {Out : St → Type v}
    (round : (s : St) → FreeM P (Out s))
    (step : (s : St) → Transcript (round s) → St) : St → Type (max uB z)
  | done (s : St) : Telescope round step s
  | extend (s : St)
      (cont : (tr : Transcript (round s)) → Telescope round step (step s tr)) :
      Telescope round step s

namespace Telescope

variable {St : Type z} {Out : St → Type v} {round : (s : St) → FreeM P (Out s)}
    {step : (s : St) → Transcript (round s) → St}

/-- Flatten a telescope into a single `FreeM` tree by iterated dependent
append, using `finish` at terminal states. -/
def toFreeM {β : Type t} (finish : St → FreeM P β) :
    {s : St} → Telescope round step s → FreeM P β
  | _, .done s => finish s
  | _, .extend s cont => append (round s) fun tr => (cont tr).toFreeM finish

@[simp]
theorem toFreeM_done {β : Type t} (finish : St → FreeM P β) (s : St) :
    (Telescope.done (round := round) (step := step) s).toFreeM finish =
      finish s := rfl

@[simp]
theorem toFreeM_extend {β : Type t} (finish : St → FreeM P β) (s : St)
    (cont : (tr : Transcript (round s)) → Telescope round step (step s tr)) :
    (Telescope.extend s cont).toFreeM finish =
      append (round s) (fun tr => (cont tr).toFreeM finish) := rfl

end Telescope


end FreeM
end PFunctor
