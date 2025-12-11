/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Comonad.Basic
import Mathlib.Data.Stream.Init

/-! # Instances of Comonads -/

universe u v -- Declare universes

namespace Id

instance : Extract Id where
  extract := id

instance : Extend Id where
  extend wx f := f wx

instance : Coseq Id where
  coseq wx wy := (wx, wy)

instance : Coapplicative Id where
  -- Functor instance is already available for Id

instance : Comonad Id where
  -- Relies on default map implementation `extend wa (f ∘ extract)`

-- Lawfulness Proofs for Id

instance : LawfulCoapplicative Id where
  id_map := by simp [Functor.map]
  comp_map := by simp [Functor.map]
  map_const := by simp [Functor.mapConst, Functor.map]
  coseqLeft_eq := by simp [CoseqLeft.coseqLeft, coseqLeft, Functor.map, coseq]
  coseqRight_eq := by simp [CoseqRight.coseqRight, coseqRight, Functor.map, coseq]
  coseq_assoc := by simp [coseq, Functor.map, Equiv.prodAssoc]

instance : LawfulComonad Id where
  map_eq_extend_extract := by simp [Functor.map, extend, Extract.extract]
  extend_extract := by simp [extend, Extract.extract]
  extract_extend := by simp [extract, extend]
  extend_assoc := by simp [extend]

end Id

namespace Prod

variable {ε : Type u}

instance : Extract (Prod ε) where
  extract := Prod.snd -- Extract the value part

instance : Extend (Prod ε) where
  extend wx f := (wx.1, f wx) -- Keep the environment, compute new value from old context

instance : Functor (Prod ε) where -- Need Functor explicitly for Coapplicative
  map f wx := (wx.1, f wx.2)

instance : Coseq (Prod ε) where
  coseq wx wy := (wx.1, (wx.2, wy.2)) -- Environment must match, assume wx.1 = wy.1 implicitly
  -- Note: A stricter version might require `wx.1 = wy.1` as a hypothesis.

-- Let Lean synthesize from base instances and defaults
instance : Coapplicative (Prod ε) where
  -- Functor, Extract, Coseq instances are defined above.
  -- coseqLeft and coseqRight will use the defaults from Coapplicative class definition.

-- Let Lean synthesize from base instances
instance : Comonad (Prod ε) where
  -- Coapplicative and Extend instances are defined above.
  -- map will use the default from Comonad class definition.

-- Lawfulness Proofs for Prod ε

instance : LawfulFunctor (Prod ε) where
  id_map := by simp [Functor.map]
  comp_map := by simp [Functor.map]
  map_const := by simp [Functor.mapConst, Functor.map]

instance : LawfulCoapplicative (Prod ε) where
  -- Inherits LawfulFunctor proofs
  coseqLeft_eq := by intros; simp [coseqLeft]
  coseqRight_eq := by intros; simp [coseqRight]
  coseq_assoc := by
    intros α β γ wa wb wc
    apply Prod.ext
    · -- Goal: (map (Equiv.prodAssoc α β γ) (coseq (coseq wa wb) wc)).1 = (coseq wa (coseq wb wc)).1
      simp only [coseq, Functor.map]
    · -- Goal: (map (Equiv.prodAssoc α β γ) (coseq (coseq wa wb) wc)).2 = (coseq wa (coseq wb wc)).2
      simp only [coseq, Functor.map, Equiv.prodAssoc_apply]

instance : LawfulComonad (Prod ε) where
  -- Inherits LawfulCoapplicative proofs
  map_eq_extend_extract := by simp [Functor.map, extend, extract]
  extend_extract := by simp [extend, extract]
  extract_extend := by simp [extract, extend]
  extend_assoc := by simp [extend]

end Prod

-- Definition of NonEmptyList --

/-- A list guaranteed to have at least one element. -/
structure NonEmptyList (α : Type u) where
  head : α
  tail : List α

deriving Repr, DecidableEq

namespace NonEmptyList
variable {α β : Type u} -- Declare universes here

/-- Convert a `NonEmptyList` to a `List`. -/
def toList (nel : NonEmptyList α) : List α := nel.head :: nel.tail

/-- Create a `NonEmptyList` from a `List` if it's non-empty. -/
def fromList? : List α → Option (NonEmptyList α)
  | [] => none
  | h :: t => some ⟨h, t⟩

/-- Map a function over a `NonEmptyList`. -/
def map (f : α → β) : NonEmptyList α → NonEmptyList β
  | ⟨h, t⟩ => ⟨f h, List.map f t⟩

-- Need LawfulFunctor instance for this map later

/-- Get the head of the `NonEmptyList` (extract). -/
@[simp] def head_nel (nel : NonEmptyList α) : α := nel.head

/-- Zip two `NonEmptyList`s. The resulting list length is the minimum of the two input lengths. -/
def zip : NonEmptyList α → NonEmptyList β → NonEmptyList (α × β)
  | ⟨h₁, t₁⟩, ⟨h₂, t₂⟩ => ⟨(h₁, h₂), List.zip t₁ t₂⟩

/-- Generate the non-empty list of non-empty tails of a `NonEmptyList`. -/
def tails : NonEmptyList α → NonEmptyList (NonEmptyList α)
  | nel@⟨_, t⟩ =>
    -- The first element of the tails is always the original list
    let head_tail : NonEmptyList α := nel
    -- The rest are the tails of the tail, mapped via fromList?
    let rest_tails_list : List (NonEmptyList α) :=
      List.filterMap NonEmptyList.fromList? (List.tails t)
    ⟨head_tail, rest_tails_list⟩ -- Construct the NonEmptyList directly

@[simp]
theorem head_tails_eq (s : NonEmptyList α) : (tails s).head = s := by
  cases s; simp [tails] -- Use cases and simp

end NonEmptyList

-- Define instances for Stream
namespace Stream'
variable {α β γ : Type u}

instance : Functor Stream' where
  map := Stream'.map

instance : Extract Stream' where
  extract := Stream'.head

instance : Extend Stream' where
  extend s f := fun n => f (Stream'.drop n s) -- Correct definition

instance : Coseq Stream' where
  coseq := Stream'.zip Prod.mk -- Provide Prod.mk

instance : CoseqLeft Stream' where
  coseqLeft s₁ _ := s₁

instance : CoseqRight Stream' where
  coseqRight _ s₂ := s₂

instance : Coapplicative Stream' where

instance : Comonad Stream' where

-- Lawfulness Proofs for Stream'

instance : LawfulFunctor Stream' where
  id_map := by
    intros α s; apply Stream'.ext; intro n
    simp [Functor.map, Stream'.map, Stream'.get]
  comp_map := by
    intros α β γ g h s; apply Stream'.ext; intro n
    simp [Functor.map, Stream'.map, Stream'.get, Function.comp_apply]
  map_const := by
    intros
    simp [Functor.mapConst, Functor.map]

instance : LawfulCoapplicative Stream' where
  coseqLeft_eq := by
    intros α β s₁ s₂; apply Stream'.ext; intro n
    -- Explicitly state the default definition in simp
    simp [CoseqLeft.coseqLeft, Functor.map, coseq, Stream'.map, Stream'.zip, Stream'.get]
  coseqRight_eq := by
    intros α β s₁ s₂; apply Stream'.ext; intro n
    -- Explicitly state the default definition in simp
    simp [CoseqRight.coseqRight, Functor.map, coseq, Stream'.map, Stream'.zip, Stream'.get]
  coseq_assoc := by
    intros α β γ s₁ s₂ s₃; apply Stream'.ext; intro n
    simp only [Functor.map, coseq, Stream'.map, Stream'.get, Stream'.zip, Equiv.prodAssoc_apply]

instance : LawfulComonad Stream' where
  map_eq_extend_extract := by
    intros α β f s; apply Stream'.ext; intro n
    simp [Functor.map, extend, extract, Stream'.map, Stream'.get, Stream'.head, Stream'.drop,
      Function.comp_apply]
  extend_extract := by
    intros wa f
    simp [extend, extract, Stream'.head, Stream'.get, Stream'.drop]
  extract_extend := by
    intros wa
    simp [extend, extract, Stream'.head, Stream'.get]
  extend_assoc := by
    intros α β γ s f g
    dsimp [extend] -- Unfold extend first
    ext n
    simp [Stream'.get, Stream'.drop_drop]
    congr 1
    ext n'
    simp
    sorry

end Stream'

-- Define instances for NonEmptyList
namespace NonEmptyList
variable {α β γ : Type u}

-- Helper theorem for LawfulFunctor
theorem map_map (g : α → β) (h : β → γ) (nel : NonEmptyList α) : map h (map g nel) = map (h ∘ g) nel := by
  cases nel; simp [map, List.map_map, Function.comp_apply]

instance : Functor NonEmptyList where
  map := NonEmptyList.map

instance : Extract NonEmptyList where
  extract := NonEmptyList.head_nel -- Use defined head

instance : Extend NonEmptyList where
  extend s f := NonEmptyList.map f (NonEmptyList.tails s) -- Use defined tails

instance : Coseq NonEmptyList where
  coseq := NonEmptyList.zip -- Use defined zip

instance : Coapplicative NonEmptyList where
  -- Uses Functor, Extract, Coseq defined above

instance : Comonad NonEmptyList where
  -- Uses Coapplicative and Extend defined above

-- Lawfulness Proofs (Sketch - may require more detailed proofs)

instance : LawfulFunctor NonEmptyList where
  id_map := by
    intro α ⟨hd, tl⟩
    simp only [Functor.map, map, id, List.map_id_fun]
  comp_map := by
    intros
    simp [Functor.map, NonEmptyList.map_map]
  map_const := by
    intro
    simp [Functor.map, Functor.mapConst]

instance : LawfulCoapplicative NonEmptyList where
  coseqLeft_eq := by
    intros
    simp [CoseqLeft.coseqLeft, Functor.map, zip, NonEmptyList.map]
  coseqRight_eq := by
    intros
    simp [CoseqRight.coseqRight, Functor.map, zip, NonEmptyList.map]
  coseq_assoc := by
    intros
    simp [Functor.map, coseq, zip, NonEmptyList.map, Equiv.prodAssoc]
    sorry

instance : LawfulComonad NonEmptyList where
  map_eq_extend_extract := sorry -- by intros; simp [Functor.map, extend, extract, NonEmptyList.map_map, NonEmptyList.map_cons, tails, head_tails] -- Needs careful proof
  extend_extract := sorry -- by intros; simp [extend, extract, tails, head_tails, NonEmptyList.map_cons] -- Needs careful proof
  extract_extend := sorry -- by intros; simp [extract, extend, NonEmptyList.head_map, head_tails]
  extend_assoc := sorry -- by intros; simp [extend, NonEmptyList.map_map] -- Very complex proof

end NonEmptyList

-- Definition of List.Zipper --

/-- Represents a List with a distinguished element ('focus'), and elements to the left and right.
    The list `left` is typically stored reversed for efficient modification near the focus. -/
structure List.Zipper (α : Type u) where
  left   : List α -- Elements to the left of the focus (reversed)
  focus  : α      -- The focused element
  right  : List α -- Elements to the right of the focus

deriving Repr, DecidableEq

-- Define instances for List.Zipper
namespace List.Zipper
variable {α β γ : Type u}

/-- Map a function over the elements of the Zipper. -/
@[simp]
def map (f : α → β) (z : Zipper α) : Zipper β :=
  ⟨ List.map f z.left, f z.focus, List.map f z.right ⟩

/-- Extract the focused element. -/
@[simp]
def extract (z : Zipper α) : α := z.focus

-- Extend via duplicate
-- Need Zipper.duplicate : Zipper α → Zipper (Zipper α)
-- This typically involves generating zippers focused on neighboring elements.
@[simp]
def duplicate (z : Zipper α) : Zipper (Zipper α) :=
  -- This requires constructing zippers focused on each position, which is complex.
  sorry -- Placeholder

-- Coseq is often derived from extend/map/extract for Zippers, or defined via a zip operation.
def coseq (za : Zipper α) (zb : Zipper β) : Zipper (α × β) :=
  sorry -- Placeholder: How to define coseq?

-- Instances (referencing the definitions above)

instance : Functor Zipper where
  map := map

instance : Extract Zipper where
  extract := extract

instance : Extend Zipper where
  extend z f := map f (duplicate z)

instance : Coapplicative Zipper where
  coseq := coseq

instance : Comonad Zipper where
  -- Uses Coapplicative and Extend defined above

-- Lawfulness Proofs (Sketch - Require Zipper API and proofs)

instance : LawfulFunctor Zipper where
  id_map    := sorry
  comp_map  := sorry
  map_const := sorry

instance : LawfulCoapplicative Zipper where
  coseqLeft_eq  := sorry
  coseqRight_eq := sorry
  coseq_assoc   := sorry

instance : LawfulComonad Zipper where
  map_eq_extend_extract := sorry -- Often true by definition if map is derived from extend
  extend_extract        := sorry -- Relates duplicate and extract
  extract_extend        := sorry -- Relates extract and map/duplicate
  extend_assoc          := sorry -- Relates map and duplicate associativity

end List.Zipper

/-! ## Comonad Transformers -/

-- Declare universes such that the arguments to w fit its expected input type
universe u₁ u₂ v₂

/-- The Environment Comonad Transformer `EnvT`.
    Adds a static environment `e` to a base comonad `w`. -/
-- Here, `a` must fit into w's input universe `u₂`.
structure EnvT (e : Type u₁) (w : Type u₂ → Type v₂) (a : Type u₂) where
  /-- The underlying comonadic value, potentially dependent on the environment (though often not directly). -/
  runEnvT : w a
  /-- The environment value. Stored alongside, but conceptually outside the base comonad `w`. -/
  env : e

namespace EnvT

variable {e : Type u₁} {w : Type u₂ → Type v₂}

-- Functor instance
instance instFunctor [Functor w] : Functor (EnvT e w) where
  map f envt := { runEnvT := Functor.map f envt.runEnvT, env := envt.env }

-- Extract instance
instance instExtract [Extract w] : Extract (EnvT e w) where
  extract envt := Extract.extract envt.runEnvT

-- Extend instance
instance instExtend [Extend w] : Extend (EnvT e w) where
  extend envt k := { runEnvT := Extend.extend envt.runEnvT (fun w'a => k { runEnvT := w'a, env := envt.env }), env := envt.env }

-- Duplicate definition (derived from extend)
-- def duplicate [Extend w] {a : Type u₂} (envt : EnvT e w a) : EnvT e w (EnvT e w a) :=
--   extend envt id

-- Coseq instance (Requires Coseq w)
-- Note: This assumes the environments are the same, which is typical usage.
-- A stricter version might require envt_a.env = envt_b.env.
instance instCoseq [Coseq w] : Coseq (EnvT e w) where
  coseq envt_a envt_b := { runEnvT := Coseq.coseq envt_a.runEnvT envt_b.runEnvT, env := envt_a.env }

-- Coapplicative instance
instance instCoapplicative [Coapplicative w] : Coapplicative (EnvT e w) where
  -- Uses instFunctor, instExtract, instCoseq defined above
  -- coseqLeft and coseqRight use default implementations

-- Comonad instance
instance instComonad [Comonad w] : Comonad (EnvT e w) where
  -- Uses instCoapplicative and instExtend defined above
  -- map uses default implementation: extend envt (fun wa => f (extract wa))

-- Lawfulness (Sketch - requires proofs based on w's lawfulness)

instance instLawfulFunctor [Comonad w] [LawfulFunctor w] : LawfulFunctor (EnvT e w) where
  id_map := by intros α wa; cases wa; simp [Functor.map, id_map]
  comp_map := by intros α β γ g h wa; cases wa; simp [Functor.map, comp_map]
  map_const := by intros; rfl

instance instLawfulCoapplicative [Comonad w] [LawfulCoapplicative w] : LawfulCoapplicative (EnvT e w) where
  -- Requires LawfulFunctor w
  coseqLeft_eq := by intros α β wa wb; cases wa; cases wb; simp [coseqLeft, Functor.map,
    Coseq.coseq]
  coseqRight_eq := by intros α β wa wb; cases wa; cases wb; simp [coseqRight, Functor.map,
    Coseq.coseq]
  coseq_assoc := sorry -- Requires underlying coseq_assoc proof for w

instance instLawfulComonad [Comonad w] [LawfulComonad w] : LawfulComonad (EnvT e w) where
  -- Requires LawfulCoapplicative w
  map_eq_extend_extract := by intros α β f wa; cases wa; simp [Functor.map, extend, extract, map_eq_extend_extract, Function.comp_apply]; sorry
  extend_extract := by intros α wa; cases wa; simp [extend, extract, extend_extract]
  extract_extend := by intros α β wa f; cases wa; simp [extend, extract, extract_extend]
  extend_assoc := sorry -- Requires underlying extend_assoc proof for w, very complex

end EnvT

/-- The Store Comonad Transformer `StoreT`.
    Adds a positional state `s` to a base comonad `w`, where `w` contains a function
    that depends on the state `s` to produce the value `a`. -/
-- Here, `s → a` must fit into w's input universe `u₂`. This requires both `s` and `a` to be in `u₂`.
structure StoreT (s : Type u₂) (w : Type u₂ → Type v₂) (a : Type u₂) where
  /-- The underlying comonadic value, which contains the function to produce `a` from `s`. -/
  runStoreT : w (s → a)
  /-- The current state or position. -/
  pos : s

namespace StoreT

variable {s : Type u₂} {w : Type u₂ → Type v₂}

-- Functor instance
instance instFunctor [Functor w] : Functor (StoreT s w) where
  map f storet := { runStoreT := Functor.map (fun g => f ∘ g) storet.runStoreT, pos := storet.pos }

-- Extract instance
instance instExtract [Comonad w] : Extract (StoreT s w) where
  extract storet := Extract.extract storet.runStoreT storet.pos

-- Extend instance
instance instExtend [Comonad w] : Extend (StoreT s w) where
  extend storet k := { runStoreT := Extend.extend storet.runStoreT (fun w'sa s' => k { runStoreT := w'sa, pos := s' }), pos := storet.pos }

-- Duplicate definition (derived from extend)
-- def duplicate [Comonad w] {a : Type u₂} (storet : StoreT s w a) : StoreT s w (StoreT s w a) :=
--   extend storet id

-- Coseq instance (Requires Comonad w for map/coseq)
instance instCoseq [Comonad w] : Coseq (StoreT s w) where
  coseq storet_a storet_b :=
    let run_ab := Coseq.coseq storet_a.runStoreT storet_b.runStoreT -- w ((s → a) × (s → b))
    let run_prod_s := Functor.map (fun (f, g) s' => (f s', g s')) run_ab -- w (s → a × b)
    { runStoreT := run_prod_s, pos := storet_a.pos }
    -- Keep first position? Or combine? Let's keep first.

-- Coapplicative instance
instance instCoapplicative [Comonad w] : Coapplicative (StoreT s w) where
  -- Uses instFunctor, instExtract, instCoseq defined above

-- Comonad instance
instance instComonad [Comonad w] : Comonad (StoreT s w) where
  -- Uses instCoapplicative and instExtend defined above

-- Lawfulness (Sketch - requires proofs based on w's lawfulness)

instance instLawfulFunctor [Comonad w] [LawfulFunctor w] : LawfulFunctor (StoreT s w) where
  id_map := by intros α wa; cases wa; simp [Functor.map]
  comp_map := by intros α β γ g h wa; cases wa; simp [Functor.map, Function.comp_assoc]
  map_const := by intros; rfl

instance instLawfulCoapplicative [Comonad w] [LawfulCoapplicative w] : LawfulCoapplicative (StoreT s w) where
  coseqLeft_eq := sorry -- Proof involves map/coseq interaction
  coseqRight_eq := sorry -- Proof involves map/coseq interaction
  coseq_assoc := sorry -- Requires underlying coseq_assoc proof for w and map properties

instance instLawfulComonad [Comonad w] [LawfulComonad w] : LawfulComonad (StoreT s w) where
  map_eq_extend_extract := sorry -- Complex proof involving extend/extract interaction
  extend_extract := sorry -- Complex proof involving extend/extract interaction
  extract_extend := by intros α β wa f; cases wa; simp [extend, extract, extract_extend]
  extend_assoc := sorry -- Requires underlying extend_assoc proof for w, very complex

end StoreT

/-! ## Day Convolution -/

-- Reuse universes declared for transformers. Add v₁ and u₃.
universe v₁ u₃

/-- The Day convolution of two functors `f` and `g`.
    It captures an operation combining elements from `f α` and `g β`
    to produce a result of type `a`, where `α` and `β` are existentially quantified. -/
structure Day (f : Type u₁ → Type v₁) (g : Type u₂ → Type v₂) (a : Type u₃) where
  /-- The underlying type for the first functor component. -/
  {α : Type u₁}
  /-- The underlying type for the second functor component. -/
  {β : Type u₂}
  /-- The function combining elements from the underlying types. -/
  map' : α → β → a
  /-- The value from the first functor. -/
  fa : f α
  /-- The value from the second functor. -/
  gb : g β

namespace Day

variable {f : Type u₁ → Type v₁} {g : Type u₂ → Type v₂}

-- Need Functor f and Functor g constraints for Comonad instance later
instance instFunctor [Functor f] [Functor g] : Functor (Day f g) where
  map {a b : Type u₃} (k : a → b) (day : Day f g a) : Day f g b :=
    -- Access fields using dot notation
    ⟨fun (x : day.α) (y : day.β) => k (day.map' x y), day.fa, day.gb⟩

@[simp]
theorem map_mk [Functor f] [Functor g] {α : Type u₁} {β : Type u₂} {a b : Type u₃} (k : a → b) (map' : α → β → a) (fa : f α) (gb : g β) :
  k <$> (⟨map', fa, gb⟩ : Day f g a) = ⟨fun x y => k (map' x y), fa, gb⟩ := rfl

/-- Define `extract` for the Day comonad. -/
def extract [Extract f] [Extract g] {a : Type u₃} (day : Day f g a) : a :=
  -- Access fields using dot notation
  day.map' (Extract.extract day.fa) (Extract.extract day.gb)

/-- Define `duplicate` for the Day comonad. -/
def duplicate [Comonad f] [Comonad g] {a : Type u₃} (day : Day f g a) : Day f g (Day f g a) :=
  sorry -- Proof is complex and encountering type/universe issues
  -- let map_dup : f day.α → g day.β → Day f g a := fun fa' gb' => @Day.mk f g a day.α day.β day.map' fa' gb'
  -- ⟨map_dup, duplicate day.fa, duplicate day.gb⟩

/-- Define `coseq` for the Day comonad. -/
def coseq [Comonad f] [Comonad g] {a b : Type u₃} (day_a : Day f g a) (day_b : Day f g b) : Day f g (a × b) :=
  -- New map function combines results using the original maps
  let map_c := fun (x : day_a.α × day_b.α) (y : day_a.β × day_b.β) =>
                 (day_a.map' x.1 y.1, day_b.map' x.2 y.2)
  -- Combine underlying functor values using their coseq
  ⟨map_c, Coseq.coseq day_a.fa day_b.fa, Coseq.coseq day_a.gb day_b.gb⟩

instance instCoseq [Comonad f] [Comonad g] : Coseq (Day f g) where
  coseq := coseq

-- Requires Functor f/g because Comonad extends Functor
-- Also requires Coseq f/g for the Day coseq definition
instance [Comonad f] [Comonad g] : Comonad (Day f g) where
  extract {a : Type u₃} := extract
  extend {a b : Type u₃} (day : Day f g a) (k : Day f g a → b) : Day f g b :=
    sorry -- Proof encountering universe issues
    -- Functor.map k (duplicate day)
  coseq {a b : Type u₃} := coseq -- Provide the coseq field

end Day
