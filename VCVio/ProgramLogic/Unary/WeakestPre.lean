-- import VCVio.OracleComp.OracleComp

-- /-!
--   # Program Logic for `FreeMonad`

--   We build a program logic for `FreeMonad` based on the paper
--     [Program Logic a la Carte](https://dl.acm.org/doi/pdf/10.1145/3704847).

--   While that paper uses `ITree`, it is essentially the same as `FreeMonad`, so adapting their work
--   is straightforward.
-- -/

-- universe u v w

-- open OracleSpec

-- alias StateT.put := StateT.set

-- local instance {α} : Zero (Option α) where
--   zero := none

-- local instance {α} : {x : Option α} → Decidable (x ≠ 0) := fun {x} => match x with
--   | none => isFalse (by intro h; contradiction)
--   | some _ => isTrue (by intro h; contradiction)

-- local instance {α} : DecidablePred (fun x : Option α => x = none) := fun n => match n with
--   | none => isTrue (by rfl)
--   | some _ => isFalse (by intro h; contradiction)

-- /-- A heap of values of type `V` is a finite map from locations (indexed by `Nat`) to values of type `V`. -/
-- @[reducible]
-- def Heap (V : Type u) := Π₀ _ : Nat, (Option V)

-- namespace Heap

-- variable {V : Type u}

-- def update (l : Nat) (v : V) : Heap V → Heap V :=
--   fun h => DFinsupp.update h l (some v)

-- def size (heap : Heap V) : Nat := heap.support.card

-- /-- Return the first free location in the heap. -/
-- def findFree (heap : Heap V) : Nat :=
--   @Nat.find (fun n => heap n = none) _ (by simp; sorry)

-- end Heap


-- /-- Interaction trees. There are two main differences with `OracleComp`:

-- 1. We have an extra constructor `tau` for a "do nothing" step (and we don't have `failure` option).

-- 2. The visible event's continuation `t : α → ITree E α` takes

-- This definition of `ITree` is also different from the Coq version, in that it's **inductive** (e.g. least fix point) and not **co-inductive** (e.g. largest fix point). Hence we cannot reason about infinite `ITree`s, but this is also not a focus in our work. -/
-- inductive ITree (E : Type u → Type v) (α : Type u) where
--   | pure (a : α)
--   | tau (t : ITree E α)
--   | vis (e : E α) (t : α → ITree E α)

-- -- Actually, inductive `ITree` without `tau` is **exactly** `FreeMonad`!
-- #check FreeMonad
-- #print OracleSpec.OracleQuery

-- /-! ## Definitions of common events -/

-- namespace Event

-- /-- The empty event type, has no inductive constructors. -/
-- inductive Void : Type u → Type v

-- instance {α : Type u} : IsEmpty (Void α) where
--   false := fun x => match x with | y => by contradiction

-- /-- The failure event for interaction trees, has a single event `fail : Fail α` -/
-- inductive Fail (α : Type u) : Type v where
--   | fail

-- /-- The state event, parametrized by the state type `σ`, comes with two operations:

-- 1. `get : State σ σ` to get the current state.
-- 2. `put (s : σ) : State σ PUnit` to set the current state. -/
-- inductive State (σ : Type u) : Type u → Type u where
--   | get : State σ σ
--   | put (s : σ) : State σ PUnit

-- /-- The type of events for a heap of values of type `V`. -/
-- def Heap (V : Type u) := State (_root_.Heap V)

-- variable {V : Type u}

-- /-- Load the value at location `l` in the heap. Returns `none` if the location is not allocated. -/
-- def Heap.load (l : Nat) : FreeMonad (Heap V) (Option V) := do
--   let s ← .lift State.get
--   return s l

-- /-- Store a value at location `l` in the heap. Returns the value that was previously at that
--   location (or `none` if the location was not allocated). -/
-- def Heap.store (l : Nat) (v : V) : FreeMonad (Heap V) (Option V) := do
--   let s ← .lift State.get
--   .lift <| State.put (s.update l v)
--   return s l

-- /-- Allocate a new location in the heap, returning the location index. -/
-- def Heap.alloc (v : V) : FreeMonad (Heap V) (ULift Nat) := do
--   let s ← .lift State.get
--   let l := s.findFree
--   .lift <| State.put (s.update l v)
--   return l

-- /-- The event type for non-determinism, comes with a single event `choose` to non-deterministically
--   choose an element of a given type. This will be handled / interpreted as either angelic (there
--   exists a choice) or demonic (for all choices). -/
-- inductive NonDet : Type u → Type v where
--   | choose (α : Type u) : NonDet α

-- /-- The sum of two event types. -/
-- def sum (E₁ : Type u → Type v) (E₂ : Type u → Type w) : Type u → Type (max v w) :=
--   fun α => E₁ α ⊕ E₂ α

-- @[inherit_doc] infixr:30 " ⊕ₑ " => sum

-- def sumEquivVoidLeft {E : Type u → Type v} {α : Type u} : (Void ⊕ₑ E) α ≃ E α where
--   toFun := fun x => match x with | .inr y => y
--   invFun := fun x => .inr x
--   left_inv := by intro x; simp; split; rfl
--   right_inv := by intro x; rfl

-- def sumEquivVoidRight {E : Type u → Type v} {α : Type u} : (E ⊕ₑ Void) α ≃ E α where
--   toFun := fun x => match x with | .inl y => y
--   invFun := fun x => .inl x
--   left_inv := by intro x; simp; split; rfl
--   right_inv := by intro x; rfl

-- def sumList (l : List (Type u → Type v)) : Type u → Type v :=
--   l.foldr (fun E E' => E ⊕ₑ E') Void

-- /-- The handler for a given event (needs to replace `Prop` with `iProp` once integrated with Iris).

-- Consists of a predicate on an event and a continuation condition, and the hypothesis that the
-- predicate is monotone.

-- Note on the monotone condition: when we integrate with Iris, we will need to replace `→` with `-*`,
-- and add `□` to the second hypothesis.
--   -/
-- structure Handler (E : Type u → Type v) where
--   toFun : {α : Type u} → E α → (α → Prop) → Prop
--   is_mono {α : Type u} {Φ Φ' : α → Prop} (hΦ : ∀ a, Φ a → Φ' a) (e : E α) : toFun e Φ → toFun e Φ'

-- instance {E} : CoeFun (Handler E) (fun _ => {α : Type u} → E α → (α → Prop) → Prop) where
--   coe := Handler.toFun

-- namespace Handler

-- variable {E E₁ : Type u → Type v} {E₂ : Type u → Type w}

-- /-- The handler for the sum of two event types, given individual handlers for each event type. -/
-- def sum (H₁ : Handler E₁) (H₂ : Handler E₂) : Handler (E₁ ⊕ₑ E₂) where
--   toFun := Sum.elim H₁.toFun H₂.toFun
--   is_mono := fun hΦ e h => by
--     match e with
--     | .inl e => exact H₁.is_mono hΦ e h
--     | .inr e => exact H₂.is_mono hΦ e h

-- @[inherit_doc] infixr:30 " ⊕ₕ " => sum

-- variable {H : Handler E} {H₁ : Handler E₁} {H₂ : Handler E₂}

-- @[simp]
-- theorem sum_inl_apply {α : Type u} {e : E₁ α} {Φ : α → Prop} :
--     (H₁ ⊕ₕ H₂).toFun (Sum.inl e) Φ = H₁ e Φ := rfl

-- @[simp]
-- theorem sum_inr_apply {α : Type u} {e : E₂ α} {Φ : α → Prop} :
--     (H₁ ⊕ₕ H₂).toFun (Sum.inr e) Φ = H₂ e Φ := rfl

-- end Handler

-- /-- The handler for the failure event, which sends everything to `False`. -/
-- def handleFail : Handler Fail where
--   toFun := fun e _ => False
--   is_mono := fun hΦ e h => by simp [h]

-- /-- The handler for angelic non-determinism, which asserts that there exists some value that
--   satisfies the continuation. -/
-- def handleNonDetAngelic : Handler NonDet where
--   toFun := fun e Φ => match e with | .choose _ => ∃ a, Φ a
--   is_mono := fun hΦ e h => match e with
--     | .choose _ => let ⟨a, h⟩ := h; ⟨a, hΦ a h⟩

-- /-- The handler for demonic non-determinism, which asserts that all values must satisfy the
--   continuation. -/
-- def handleNonDetDemonic : Handler NonDet where
--   toFun := fun e Φ => match e with | .choose _ => ∀ a, Φ a
--   is_mono := fun hΦ e h => match e with
--     | .choose _ => by simp_all

-- /-- The handler for the state event, parametrized by a predicate on the state (i.e. a state
--   interpretation). -/
-- def handleState {σ} (S : σ → Prop) : Handler (State σ) where
--   -- This really doesn't make sense until we integrate with Iris.
--   toFun := fun e Φ => match e with
--     -- S s -* ⇛(S s * Φ s)
--     | .get => ∀ s, S s → (S s ∧ Φ s)
--     -- S s -* ⇛(S s' * Φ _)
--     | .put s' => ∀ s, S s → (S s' ∧ Φ PUnit.unit)
--   is_mono := fun {α Φ Φ'} hΦ e h => by
--     cases e <;> simp_all
--     exact fun s hs => ⟨(h s hs).1, hΦ _ (h s hs).2⟩

-- /-- The handler for the heap event, parametrized by a heap interpretation (heap invariant?).

-- TODO: re-examine this. -/
-- def handleHeap {V} (S : _root_.Heap V → Prop) : Handler (Heap V) :=
--   handleState S

-- -- Handling oracle queries?? We probably need Iris here since we are mapping to `PMF` instead of `Prop`

-- end Event

-- open Event

-- namespace FreeMonad

-- variable {E : Type u → Type v} {E' : Type u → Type w} {α β : Type u}

-- section Sum

-- /-- Lift a `FreeMonad E α` to a `FreeMonad (E ⊕ₑ E') α` by injecting into the left component. -/
-- def inl : FreeMonad E α → FreeMonad (E ⊕ₑ E') α :=
--   FreeMonad.mapM (fun a => .lift (Sum.inl a))
--   -- | .pure a => .pure a
--   -- | .roll e r => .roll (Sum.inl e) (fun a => inl (r a))

-- /-- Lift a `FreeMonad E' α` to a `FreeMonad (E ⊕ₑ E') α` by injecting into the right component. -/
-- def inr : FreeMonad E' α → FreeMonad (E ⊕ₑ E') α :=
--   FreeMonad.mapM (fun a => .lift (Sum.inr a))
--   -- | .pure a => .pure a
--   -- | .roll e r => .roll (Sum.inr e) (fun a => inr (r a))

-- @[simp]
-- def inl_apply {x : FreeMonad E α} :
--   (inl x : FreeMonad (E ⊕ₑ E') α) = FreeMonad.mapM (fun a => .lift (Sum.inl a)) x := rfl

-- @[simp]
-- def inr_apply {x : FreeMonad E' α} :
--   (inr x : FreeMonad (E ⊕ₑ E') α) = FreeMonad.mapM (fun a => .lift (Sum.inr a)) x := rfl

-- end Sum

-- section WeakestPre

-- /-- Weakest precondition of a `FreeMonad` program, with respect to a postcondition and a handler for
--   the events.

--   When we integrate with Iris, we will need to wrap the update modality `⇛` around this. -/
-- def wp (H : Handler E) (Φ : α → Prop) : FreeMonad E α → Prop
--   | .pure a => Φ a
--   | .roll e r => H e (fun a => wp H Φ (r a))

-- variable {H : Handler E} {Φ Φ' : α → Prop}

-- -- For the theorems below, we will replace `↔` with bi-implication `⊣⊢` once integrated with Iris.

-- /-- The weakest precondition of a pure program is equivalent to the postcondition applied to the
--   result. -/
-- @[simp]
-- theorem wp_pure {a : α} : wp H Φ (FreeMonad.pure a) ↔ Φ a := by simp [wp]

-- /-- The weakest precondition of a `roll` is equivalent to the handler's condition applied to the
--   weakest precondition of the continuation. -/
-- @[simp]
-- theorem wp_roll {e : E α} {r : α → FreeMonad E α} :
--     wp H Φ (FreeMonad.roll e r) ↔ H e (fun a => wp H Φ (r a)) := by simp [wp]

-- /-- The weakest precondition of an event (lifted to `FreeMonad`) is equivalent to the handler's
--   condition. -/
-- @[simp]
-- theorem wp_event {e : E α} : wp H Φ (FreeMonad.lift e) ↔ H e Φ := by simp [lift, wp]

-- /-- The weakest precondition of a `bind` is equivalent to sequencing the weakest precondition of the
--   first program with the weakest precondition of the second program. -/
-- @[simp]
-- theorem wp_bind {x : FreeMonad E β} {f : β → FreeMonad E α} :
--     wp H Φ (FreeMonad.bind x f) ↔ wp H (fun a => wp H Φ (f a)) x := by
--   induction x with
--   | pure a => simp [wp]
--   | roll e r ih => simp [wp, ih]

-- /-- The consequence rule for weakest preconditions: if `Φ` entails `Φ'`, then `wp H Φ x` entails
--   `wp H Φ' x`. -/
-- theorem wp_conseq {x : FreeMonad E α} (hΦ : ∀ a, Φ a → Φ' a) (h : wp H Φ x) : wp H Φ' x := by
--   induction x with
--   | pure a => exact hΦ a h
--   | roll e r ih => exact H.is_mono ih e h

-- alias wp_mono := wp_conseq

-- /-- The frame rule for weakest preconditions: if `P` and `wp H Φ x` hold,
--   then `wp H (fun a => P ∧ Φ a) x` holds. (does the reverse implication hold?) -/
-- @[simp]
-- theorem wp_frame {x : FreeMonad E α} {P : Prop} (hP : P) (h : wp H Φ x) :
--     wp H (fun a => P ∧ Φ a) x := by
--   induction x generalizing Φ with
--   | pure a => simp_all
--   | roll e r ih => simp_all [wp, ih]

-- variable {E' : Type u → Type w}

-- /-- Weakest precondition of `inl` is equivalent to the weakest precondition of the left component,
--   assuming the overall handler is equivalent to the handler for the left component -/
-- @[simp]
-- theorem wp_inl {H' : Handler (E ⊕ₑ E')} (hH : ∀ {α} e Φ, @H α e Φ ↔ H' (Sum.inl e) Φ) {x : FreeMonad E α} :
--     wp H' Φ (FreeMonad.inl x) ↔ wp H Φ x := by
--   induction x with
--   | pure a => simp
--   | roll e r ih =>
--     simp [wp, hH]
--     constructor <;> intro h
--     · exact H'.is_mono (fun a hwp => (ih a).mp hwp) (Sum.inl e) h
--     · exact H'.is_mono (fun a hwp => (ih a).mpr hwp) (Sum.inl e) h

-- /-- Special case of `wp_inl` when the handler is the sum of two handlers. -/
-- @[simp]
-- theorem wp_inl' {H' : Handler E'} {x : FreeMonad E α} :
--     wp (H ⊕ₕ H') Φ (FreeMonad.inl x) ↔ wp H Φ x :=
--   wp_inl (fun e Φ => by simp)

-- /-- Weakest precondition of `inr` is equivalent to the weakest precondition of the right component,
--   assuming the overall handler is equivalent to the handler for the right component -/
-- @[simp]
-- theorem wp_inr {H' : Handler (E' ⊕ₑ E)} (hH : ∀ {α} e Φ, @H α e Φ ↔ H' (Sum.inr e) Φ) {x : FreeMonad E α} :
--     wp H' Φ (.inr x) ↔ wp H Φ x := by
--   induction x with
--   | pure a => simp
--   | roll e r ih =>
--     simp [wp, hH]
--     constructor <;> intro h
--     · exact H'.is_mono (fun a hwp => (ih a).mp hwp) (Sum.inr e) h
--     · exact H'.is_mono (fun a hwp => (ih a).mpr hwp) (Sum.inr e) h

-- /-- Special case of `wp_inr` when the handler is the sum of two handlers. -/
-- @[simp]
-- theorem wp_inr' {H' : Handler E'} {x : FreeMonad E' α} :
--     wp (H ⊕ₕ H') Φ (.inr x) ↔ wp H' Φ x :=
--   wp_inr (fun e Φ => by simp)

-- /-- Weakest precondition of `fail`, given the canonical handler for `Fail`, is False. -/
-- @[simp]
-- theorem wp_fail : wp handleFail Φ (.lift $ @Fail.fail α) = False := by simp [handleFail]

-- /-- Weakest precondition of `NonDet.choose`, handled demonically, is equivalent to the postcondition
--   being true for all possible choices. -/
-- @[simp]
-- theorem wp_demonic : wp handleNonDetDemonic Φ (.lift $ @NonDet.choose α) = ∀ a, Φ a := by
--   simp [handleNonDetDemonic]

-- /-- Weakest precondition of `NonDet.choose`, handled angelically, is equivalent to the postcondition
--   being true for some possible choice. -/
-- @[simp]
-- theorem wp_angelic : wp handleNonDetAngelic Φ (.lift $ @NonDet.choose α) = ∃ a, Φ a := by
--   simp [handleNonDetAngelic]

-- -- theorem wp_get {σ} {S : σ → Prop} : wp (handleState S) (fun s => S s) (FreeMonad.lift State.get) ↔ S := by
-- --   simp [handleState]

-- -- theorem wp_put {σ} {S : σ → Prop} {s : σ} : wp (handleState S) (fun _ => S s) (FreeMonad.lift (State.put s)) ↔ S s := by
-- --   simp [handleState]

-- end WeakestPre

-- section HoareTriple

-- /-- Hoare triple for `FreeMonad` programs, defined in terms of weakest preconditions. -/
-- def hoareTriple (H : Handler E) (Ψ : Prop) (Φ : α → Prop) (x : FreeMonad E α) : Prop :=
--   -- Replace `→` with `-*` once integrated with Iris.
--   Ψ → wp H Φ x

-- variable {H : Handler E} {Ψ Ψ' : Prop} {Φ Φ' : α → Prop}

-- @[simp]
-- theorem hoareTriple_pure {a : α} : hoareTriple H Ψ Φ (FreeMonad.pure a) ↔ Ψ → Φ a := by
--   simp only [hoareTriple, wp_pure]

-- @[simp]
-- theorem hoareTriple_roll {e : E α} {r : α → FreeMonad E α} :
--     hoareTriple H Ψ Φ (FreeMonad.roll e r) ↔ Ψ → H e (fun a => wp H Φ (r a)) := by
--   simp only [hoareTriple, wp_roll]

-- @[simp]
-- theorem hoareTriple_lift {e : E α} : hoareTriple H Ψ Φ (FreeMonad.lift e) ↔ Ψ → H e Φ := by
--   simp only [hoareTriple, wp_event]

-- @[simp]
-- theorem hoareTriple_bind {x : FreeMonad E β} {f : β → FreeMonad E α} :
--     hoareTriple H Ψ Φ (FreeMonad.bind x f) ↔ Ψ → wp H (fun a => wp H Φ (f a)) x := by
--   simp only [hoareTriple, wp_bind]

-- theorem hoareTriple_conseq (hΨ : Ψ' → Ψ) (hΦ : ∀ a, Φ a → Φ' a) {x : FreeMonad E α}
--     (h : hoareTriple H Ψ Φ x) : hoareTriple H Ψ' Φ' x := by
--   intro ψ
--   exact wp_conseq hΦ (h (hΨ ψ))

-- theorem hoareTriple_weaken (hΨ : Ψ' → Ψ) {x : FreeMonad E α} (h : hoareTriple H Ψ Φ x) :
--     hoareTriple H Ψ' Φ x :=
--   hoareTriple_conseq hΨ (fun _ => id) h

-- theorem hoareTriple_strengthen (hΦ : ∀ a, Φ a → Φ' a) {x : FreeMonad E α} (h : hoareTriple H Ψ Φ x) :
--     hoareTriple H Ψ Φ' x :=
--   hoareTriple_conseq (id) hΦ h

-- @[simp]
-- theorem hoareTriple_frame {x : FreeMonad E α} {P : Prop} (hP : P) (h : hoareTriple H Ψ Φ x) :
--     hoareTriple H (P ∧ Ψ) (fun a => P ∧ Φ a) x :=
--   fun ⟨_, ψ⟩ => wp_frame hP (h ψ)

-- @[simp]
-- theorem hoareTriple_inl {H' : Handler E'} {x : FreeMonad E α} :
--     hoareTriple (H ⊕ₕ H') Ψ Φ (FreeMonad.inl x) ↔ hoareTriple H Ψ Φ x := by
--   simp [hoareTriple, wp_inl']
--   refine iff_eq_eq.mpr ?_
--   congr
--   exact iff_eq_eq.mp wp_inl'

-- @[simp]
-- theorem hoareTriple_inr {H' : Handler E'} {x : FreeMonad E' α} :
--     hoareTriple (H ⊕ₕ H') Ψ Φ (FreeMonad.inr x) ↔ hoareTriple H' Ψ Φ x := by
--   simp [hoareTriple, wp_inr']
--   refine iff_eq_eq.mpr ?_
--   congr
--   exact iff_eq_eq.mp wp_inr'

-- end HoareTriple

-- section Interpretation

-- /-- Interpret the sole `Fail` event, returning an `Option` -/
-- def interpFail : FreeMonad Fail α → Option α :=
--   FreeMonad.mapM (fun a => match a with | .fail => none)

-- /-- Interpret the `Fail` event (occurring on the left), by mapping it to `none` in the `OptionT` monad. -/
-- def interpFailLeft : FreeMonad (Fail ⊕ₑ E) α → OptionT (FreeMonad E) α :=
--   FreeMonad.mapM (fun a => match a with
--     | .inl .fail => FreeMonad.pure none
--     | .inr e => .lift e)

-- /-- Interpret the `Fail` event (occurring on the right), by mapping it to `none` in the `OptionT` monad. -/
-- def interpFailRight : FreeMonad (E ⊕ₑ Fail) α → OptionT (FreeMonad E) α :=
--   FreeMonad.mapM (fun a => match a with
--     | .inl e => .lift e
--     | .inr .fail => FreeMonad.pure none)

-- def interpState {σ} : FreeMonad (State σ) α → StateM σ α :=
--   FreeMonad.mapM (fun a => match a with | .get => StateT.get | .put s => StateT.put s)

-- def interpStateLeft {σ} : FreeMonad (State σ ⊕ₑ E) α → StateT σ (FreeMonad E) α :=
--   FreeMonad.mapM (fun a => match a with
--     | .inl .get => StateT.get
--     | .inl (.put s) => StateT.put s
--     | .inr e => .lift e)

-- def interpStateRight {σ} : FreeMonad (E ⊕ₑ State σ) α → StateT σ (FreeMonad E) α :=
--   FreeMonad.mapM (fun a => match a with
--     | .inl e => .lift e
--     | .inr .get => StateT.get
--     | .inr (.put s) => StateT.put s)

-- /-- To interpret `NonDet` demonically, we need to use a relation and not just a function. -/
-- def interpDemonicLeft {α : Type u} : FreeMonad (NonDet ⊕ₑ E) α → FreeMonad E α → Prop := sorry

-- noncomputable section

-- variable {ι} {spec : OracleSpec ι} [spec.FiniteRange]

-- /-- Interpret `OracleQuery` as a `PMF` by assuming each oracle response is uniformly distributed.

-- This is the same as the `evalDist` function on `OracleComp` (modulo the `OptionT` wrapper). -/
-- def interpOracleQuery : FreeMonad (OracleQuery spec) α → PMF α :=
--   FreeMonad.mapM (fun a => match a with | query i _ => PMF.uniformOfFintype (spec.range i))

-- -- Note: it does not seem possible to have an interpretation from
-- -- `FreeMonad (OracleQuery spec ⊕ₑ E) α` to something involving `FreeMonad E` and `PMF`

-- -- However, it is possible to map `OracleQuery spec` to `NonDet` and thus interpret oracle queries
-- -- in either angelic or demonic style

-- def interpOracleQueryAngelic : FreeMonad (OracleQuery spec ⊕ₑ E) α → FreeMonad (NonDet ⊕ₑ E) α :=
--   FreeMonad.mapM (fun a => match a with
--     | .inl (query i _) => .lift (Sum.inl (NonDet.choose (spec.range i)))
--     | .inr e => .lift (Sum.inr e))

-- -- def interpOracleQueryLeft : FreeMonad (OracleQuery spec ⊕ₑ E) α → PMF (FreeMonad E α)
-- --   | .pure a => PMF.pure (FreeMonad.pure a)
-- --   | .roll (Sum.inl (query i _)) r => PMF.bind (PMF.uniformOfFintype (spec.range i)) (fun a => interpOracleQueryLeft (r a))
-- --   | .roll (Sum.inr e) r => PMF.bind (PMF.pure (FreeMonad.lift e))
-- --     (fun a => interpOracleQueryLeft (r a))
--   -- Problem: `interpOracleQueryLeft (r b)` for some `b : β` is of type `PMF (FreeMonad E α)`
--   -- So of course there are some non-trivial bindings inside `r`

--   -- FreeMonad.mapM (f := OracleQuery spec ⊕ₑ E) (α := α) (fun a => match a with
--   --   | Sum.inl q => match q with | query i _ => FreeMonad.pure (PMF.uniformOfFintype (spec.range i))
--   --   | Sum.inr e => .lift e)

-- -- What should happen? `.lift (query i t) : FreeMonad (OracleQuery spec ⊕ₑ E) α` should be sent to
-- -- `FreeMonad.pure <$> PMF.uniformOfFintype (spec.range i) : PMF (FreeMonad E α)`?
-- -- while `.lift e : FreeMonad (OracleQuery spec ⊕ₑ E) α` should be sent to `PMF.pure (.lift e) : PMF (FreeMonad E α)`?

-- -- def interpOracleQueryRight : FreeMonad (E ⊕ₑ OracleQuery spec) α → FreeMonad E α → Prop := sorry

-- end

-- end Interpretation

-- #print and

-- section Adequacy

-- /-- Adequacy theorem for the `Fail` event occurring on the left. -/
-- theorem adequacyFailLeft {x : FreeMonad (Fail ⊕ₑ E) α} {y : OptionT (FreeMonad E) α} {H : Handler E} {Φ : α → Prop}
--     (h : interpFailLeft x = y) (hwp : wp (handleFail ⊕ₕ H) Φ x) :
--       wp H (fun a => ∃ b, a = some b ∧ Φ b) y := by
--   rw [← h]
--   induction x with
--   | pure a => simp_all [interpFailLeft, handleFail, pure, OptionT.pure, OptionT.mk, ← h]
--   | roll e r ih =>
--     simp_all [interpFailLeft, handleFail, bind, OptionT.bind, OptionT.mk, OptionT.lift, ← h, ih]
--     sorry

-- -- TODO: state & prove adequacy theorems for other events

-- end Adequacy

-- -- Note: this instance does **not** satisfy `LawfulAlternative` since the `fail` events do not collapse
-- instance : AlternativeMonad (FreeMonad (E ⊕ₑ Fail)) where
--   failure := .roll (Sum.inr $ Fail.fail) .pure
--   orElse := fun _ y => y ()

-- -- This seems wrong, there is definitely no equivalence (could there be a split injection though?)
-- def sumFailEquivOptionT (E : Type u → Type v) {α : Type u} :
--     FreeMonad (E ⊕ₑ Fail) α ≃ OptionT (FreeMonad E) α where
--   toFun := interpFailRight
--   invFun := OptionT.mapM (FreeMonad.mapM (fun e => .roll (Sum.inl e) .pure))
--   left_inv := by
--     intro x; simp [interpFailRight, OptionT.mapM, OptionT.run, pure, bind, OptionT.bind, OptionT.pure, OptionT.mk];
--     rcases x with x | x
--     · simp [pure, OptionT.pure, OptionT.mk]
--     · simp [failure, bind, OptionT.bind, OptionT.mk]
--       unfold FreeMonad.bind
--       split <;> simp_all <;> sorry
--   right_inv := by
--     intro x
--     rcases x with x | x
--     · simp [OptionT.mapM, OptionT.run]
--       rcases x
--       · simp [failure, interpFailRight]
--       · rfl
--     · simp [OptionT.mapM, OptionT.run, bind, OptionT.bind, OptionT.mk, interpFailRight, OptionT.lift]
--       congr
--       funext a
--       simp [FreeMonad.bind, failure]
--       sorry

-- end FreeMonad

-- variable {ι : Type u} {spec : OracleSpec ι} {α : Type w}

-- def OracleComp.ofFreeMonadSumFail : FreeMonad (OracleQuery spec ⊕ₑ Fail) α → OracleComp spec α :=
--   FreeMonad.interpFailRight
