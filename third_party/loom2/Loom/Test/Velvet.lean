import Lean
import Loom.Test.Driver
import Loom.Triple.SpecLemmas
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Order Std.Do' Lean.Order

section Loops

/- partial loop from MonoBind and CCPO instances -/
@[specialize, inline]
def Loop.forIn.loop {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
  match ← f () b with
    | ForInStep.done b  => pure b
    | ForInStep.yield b => loop f b
  partial_fixpoint

@[inline]
def Loop.forIn {m : Type u → Type v} {β : Type u} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  Loop.forIn.loop f init

@[instance high]
instance {m : Type u → Type v} [md : Monad m] [ccpo : ∀ α, CCPO (m α)] [mono : MonoBind m] :
    ForIn m Lean.Loop Unit where
  forIn {β} _ b f := @Loop.forIn m β md ccpo mono Loop.mk b f

variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
  [∀ α, CCPO (m α)] [MonoBind m]

theorem repeat_inv (f : Unit → β → m (ForInStep β))
    (inv : ForInStep β → Pred) (measure : β → Nat) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv (ForInStep.yield b)) (f () b)
      (fun | ForInStep.yield b' => inv (ForInStep.yield b') ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv (ForInStep.done b')) epost) :
    Triple (inv (ForInStep.yield init)) (Loop.forIn.loop f init)
      (fun b => inv (ForInStep.done b)) epost := by
  have induc (C : β → Prop) (a : β) (h : ∀ x, (∀ y, measure y < measure x → C y) → C x) : C a := by
    have lem : ∀ n : Nat, ∀ x, measure x ≤ n → C x := by
      intro n
      induction n with
      | zero =>
        intro x hx
        exact h x (fun y => by omega)
      | succ m ih =>
        intro x hx
        by_cases neq : measure x ≤ m
        · exact ih x neq
        · exact h x (fun y hy => ih y (by omega))
    exact lem (measure a) a (by simp)
  apply induc
    (fun ini => Triple (inv (ForInStep.yield ini)) (Loop.forIn.loop f ini)
      (fun b => inv (ForInStep.done b)) epost) init
  intro b ih; unfold Loop.forIn.loop
  apply Triple.bind _ _ (fun step => match step with
    | ForInStep.yield b' => inv (ForInStep.yield b') ⊓ ⌜ measure b' < measure b ⌝
    | ForInStep.done b' => inv (ForInStep.done b'))
  · exact hstep b
  · intro step; match step with
    | ForInStep.done b' => exact Triple.pure b' PartialOrder.rel_refl
    | ForInStep.yield b' =>
      apply Triple.iff.mpr
      simp [pure_intro_l]
      intro m_lt
      exact Triple.iff.mp (ih b' m_lt)

/-- Loop rule with invariant incorporated into the body: `inv` lives on `β` directly
(same predicate for yield and done), and an optional `doneWith` strengthening on exit. -/
theorem repeat_inv_split (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (doneWith : β → Pred) (measure : β → Nat) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv b' ⊓ doneWith b') epost) :
    Triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ doneWith b) epost :=
  repeat_inv f
    (fun | ForInStep.yield b => inv b | ForInStep.done b => inv b ⊓ doneWith b)
    measure epost init hstep

/-- Simplified variant when done adds no extra information. -/
theorem repeat_inv_simple (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (measure : β → Nat) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv b') epost) :
    Triple (inv init) (Loop.forIn.loop f init) (fun b => inv b) epost :=
  repeat_inv f
    (fun | ForInStep.yield b => inv b | ForInStep.done b => inv b)
    measure epost init hstep

set_option linter.unusedVariables false in
def invariantGadget (inv : Pred) : m PUnit := pure ⟨⟩
set_option linter.unusedVariables false in
def decreasingGadget (measure : Nat) : m PUnit := pure ⟨⟩
set_option linter.unusedVariables false in
def onDoneGadget {α : Type _} (done : α) : m PUnit := pure ⟨⟩

/-- Spec for `repeat do` loops (`forIn Loop.mk`). -/
@[lspec]
theorem Spec.forIn_loop
    {init : β} {f : Unit → β → m (ForInStep β)}
    {inv : β → Pred} {measure : β → Nat} {doneWith : β → Pred} {eInv : EPred}
    (step : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv b' ⊓ doneWith b') eInv) :
    Triple (inv init) (forIn Loop.mk init fun u b => do
      invariantGadget (inv b)
      decreasingGadget (measure b)
      onDoneGadget (doneWith b)
      f u b)
      (fun b => inv b ⊓ doneWith b) eInv :=
  sorry

private def foldInvariants (invs : Array (Lean.TSyntax `term)) : Lean.MacroM (Lean.TSyntax `term) := do
  if invs.isEmpty then `(True)
  else
    let mut result := invs[0]!
    for i in [1:invs.size] do
      result ← `($result ⊓ $(invs[i]!))
    return result

syntax "while' " termBeforeDo
  (" invariant " termBeforeDo)*
  " decreasing " termBeforeDo
  (" done_with " termBeforeDo)?
  " do " doSeq : doElem

macro_rules
  | `(doElem| while' $cond $[ invariant $invs]* decreasing $m done_with $d do $body) => do
    let inv ← foldInvariants invs
    `(doElem| repeat do
      invariantGadget $inv
      decreasingGadget $m
      onDoneGadget $d
      if $cond then $body else break)

macro_rules
  | `(doElem| while' $cond $[ invariant $invs]* decreasing $m do $body) => do
    let inv ← foldInvariants invs
    `(doElem| repeat do
      invariantGadget $inv
      decreasingGadget $m
      onDoneGadget (¬ $cond)
      if $cond then $body else break)


end Loops

section WhileParseTest

/-- Test that `while'` macro parses nested loops with multiple invariants. -/
def whileParseTest (xs : List Nat) : Option Nat := do
  let mut sum := 0
  let mut rest := xs
  while' rest.length > 0
  invariant sum + rest.foldl (· + ·) 0 = xs.foldl (· + ·) 0
  invariant rest.length ≤ xs.length
  decreasing rest.length
  do
    match rest with
    | [] => break  -- unreachable but needed for exhaustiveness
    | x :: tl =>
      sum := sum + x
      rest := tl
  return sum

/-- Test nested while' loops. -/
def whileNested : Option Nat := do
  let mut i := 0
  let mut total := 0
  while' i < 3
  invariant i ≤ 3
  decreasing 3 - i
  do
    let mut j := 0
    while' j < 2
    invariant j ≤ 2
    decreasing 2 - j
    do
      total := total + 1
      j := j + 1
    i := i + 1
  return total

/-- Test while' with done_with annotation. -/
def whileDoneWith (n : Nat) : Option Nat := do
  let mut k := n
  while' k > 0
  invariant k ≤ n
  decreasing k
  done_with k = 0
  do
    k := k - 1
  return k

#eval whileParseTest [1, 2, 3, 4]
#eval whileNested
#eval whileDoneWith 5

end WhileParseTest


section InsertionSort

-- @[simp]
-- theorem Array.replicate_get (n : Nat) [Inhabited α] (a : α) (i : Nat) (_ : i < n := by omega) :
--   (Array.replicate n a)[i]! = a := by
--   rw [getElem!_pos, Array.getElem_replicate]; grind

-- @[simp]
-- theorem Array.modify_get (a : Array α) [Inhabited α] (i j : Nat) (f : α -> α) :
--   (a.modify i f)[j]! = if j < a.size then if j = i then f a[j]! else a[j]! else default := by
--   grind

def Array.toMultiset (arr : Array α) [BEq α] : (α → Nat) := fun a => arr.count a

@[grind .]
theorem Array.multiset_swap [Inhabited α] [BEq α]
(arr: Array α) (idx₁ idx₂: Nat) (h_idx₁: idx₁ < arr.size) (h_idx₂: idx₂ < arr.size) :
  ((arr.set! idx₂ arr[idx₁]!).set! idx₁ arr[idx₂]!).toMultiset = arr.toMultiset := by
    sorry


def insertionSort (arr : Array Nat) : Option (Array Nat) := do
    let mut arr := arr
    let arr₀ := arr
    let arr_size := arr.size
    let mut n := 1
    while' n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant ∀ i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arr₀.toMultiset
    decreasing arr.size - n
    do
      let mut mind := n
      while' mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      invariant ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arr₀.toMultiset
      decreasing mind
      do
        if arr[mind]! < arr[mind - 1]! then
          let tmp := arr[mind - 1]!
          arr := arr.set! (mind - 1) arr[mind]!
          arr := arr.set! mind tmp
        mind := mind - 1
      n := n + 1
    return arr

@[grind .]
theorem foo2 (a : Prop) : a -> ⌜ a ⌝ := by sorry

-- set_option trace.profiler true

-- #check Sym.mkMethods

set_option trace.Loom.Tactic.vcgen.grind true

theorem foo' {α : Type u} {β : Type u} (a : α) (b : β) : (MProd.mk a b).fst = a := by rfl
theorem foo'' {α : Type u} {β : Type u} (a : α) (b : β) : (MProd.mk a b).snd = b := by rfl

def Goal (_n : Nat) := ∀ arr₀, ⦃ 1 ≤ arr₀.size ⦄ insertionSort arr₀ ⦃ arr,
      (arr.toMultiset = arr₀.toMultiset) ⊓
      (∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ arr.size - 1 → arr[i]! ≤ arr[j]!) ⦄

#eval runBenchUsingTactic ``Goal [] `(tactic| (intro arr₀; simp only [insertionSort]; mvcgen' simplifying_assumptions [foo', foo''] with grind)) `(tactic| fail) [0]

end InsertionSort

section TestPure

/-- Test: postcondition with ⌜p⌝ — VCGen should reduce to proving p. -/
theorem test_pure_post :
    ⦃ True ⦄ (pure () : Option Unit) ⦃ _, (⌜1 = 1⌝ : Prop) ⦄ := by
  mvcgen'

/-- Test: postcondition with ⌜p⌝ ⊓ q — VCGen should split and handle pure. -/
theorem test_pure_meet :
    ⦃ True ⦄ (pure () : Option Unit) ⦃ _, (⌜2 = 2⌝ : Prop) ⊓ (⌜3 = 3⌝ : Prop) ⦄ := by
  mvcgen'

end TestPure
