/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.PFunctor.Chart.Basic
import ToMathlib.PFunctor.Equiv.Basic
import ToMathlib.PFunctor.Lens.Basic

/-!
# UC interfaces and open boundaries

This file introduces the smallest structural layer for open concurrent systems.

The current concurrent semantic center, `ProcessOver`, describes closed
residual processes whose step protocols already live inside the system. For
UC-style openness, contextual plugging, and general interaction with an
environment, we also need a typed notion of:

* what traffic may enter a component,
* what traffic may leave it, and
* how such open boundaries compose.

The design here is intentionally minimal and purely structural.
Every definition is an `abbrev` over existing `PFunctor` / chart / lens
machinery, so the established theory is reused definitionally while
presenting names that read naturally in the interaction setting.

* `Interface` is `PFunctor`: ports `A` and per-port messages `B a`.
* `Interface.Packet I` is one concrete boundary message on interface `I`.
* `Interface.Hom I J` is `PFunctor.Chart I J` (forward packet transport,
  covariant on both components).
* `Interface.QueryHom I J` is `PFunctor.Lens I J` (query retargeting with
  response pullback, contravariant on the fibre).
* `Interface.Equiv I J` is the chart-level interface isomorphism.
* `Interface.comp I J` is the composition monoidal product on polynomial
  functors (`PFunctor.comp`), modelling sequential dependence where one
  interface's response determines the next interface's port.
* `Interface.compUnit` is the composition unit (the identity polynomial
  functor: one port, one message).
* `PortBoundary` is a directed pair of input and output interfaces.
* `PortBoundary.swap`, `tensor`, `empty`, and `PortBoundary.Hom` are the
  basic operations for open composition.

The most important distinction in this file is:

* `Hom` acts on packets that have already been produced.
* `QueryHom` acts on one-step observations / queries that are still waiting
  for a response.

So `Hom` pushes traffic forward, while `QueryHom` retargets an interaction and
pulls the eventual response back.
The composition product is only functorial for `QueryHom` (lenses), not for
`Hom` (charts), because the fibre-level map must be contravariant.

This file also introduces the first equivalence layer:

* `Interface.Equiv` for interface isomorphisms, and
* `PortBoundary.Equiv` for the corresponding variance-aware isomorphisms of
  directed open boundaries.

These structures are the starting point for expressing tensor unit,
associativity, and symmetry at the boundary level without hard-coding more
primitive operations into `OpenTheory`.

This file does **not** yet define open worlds, plugging, or runtime semantics.
Those later layers should build on these typed boundary primitives rather than
re-introducing their own packet/interface vocabulary.

## References

* Niu, Spivak (2024), Polynomial Functors: A Mathematical Theory of
  Interaction — the composition product, charts, lenses, and monoidal
  structures on polynomial functors used throughout this file
-/

universe uA uB vA vB wA wB

namespace Interaction
namespace UC

/--
`Interface` is the interaction-facing name for `PFunctor`.

An interface packages:

* a type of ports `A`, and
* for each port `a : A`, a type of messages `B a`.

This is the same dependent-container structure already used throughout the
existing `PFunctor` world. The point of the new name is only to reflect the
intended reading: these are typed communication interfaces.
-/
abbrev Interface := PFunctor

namespace Interface

/--
`Packet I` is one concrete message on interface `I`.

It consists of:

* a chosen port `a : I.A`, and
* a message `m : I.B a` carried on that port.

This is exactly `PFunctor.Idx I`, reused under a boundary-oriented name.
-/
abbrev Packet (I : Interface.{uA, uB}) : Type (max uA uB) :=
  PFunctor.Idx I

/--
`Query I α` is the continuation-bearing one-step query shape induced by the
interface `I`.

Unlike `Packet I`, which is just a concrete boundary message, `Query I α`
already stores a continuation returning values of type `α`.
So `Query` is the right bridge back to the existing `PFunctor` / oracle world:
it does not represent traffic that has already happened, but a one-step
interaction that is still waiting for a response.

This is exactly why the interface layer needs two different morphism notions:

* `Hom`, for translating packets that already exist, and
* `QueryHom`, for retargeting a query while reinterpreting its eventual
  response.

At the `PFunctor` level, this is also the distinction between:

* `PFunctor.Chart`, which transports concrete packets forward, and
* `PFunctor.Lens`, which transports continuation-bearing queries.
-/
abbrev Query (I : Interface.{uA, uB}) (α : Type vA) :
    Type (max uA uB vA) :=
  PFunctor.Obj I α

/--
`Hom I J` is the boundary-facing name for `PFunctor.Chart I J`.

A chart translates concrete packets forward from `I` to `J`:

* `toFunA` maps ports, and
* `toFunB` maps messages along the translated port.

In more operational terms, `Hom` answers the question:

> if a packet actually appears on interface `I`, how should it be viewed as a
> packet on interface `J`?

So `Hom` is the structural notion of interface adaptation used for concrete
boundary traffic. When later layers need continuation-preserving interface
maps, they should use `QueryHom` instead.
-/
abbrev Hom (I : Interface.{uA, uB}) (J : Interface.{vA, vB}) :=
  PFunctor.Chart I J

/--
`Equiv I J` is the structural notion of interface isomorphism.

Unlike a plain `Hom`, which only translates packets forward, an
`Interface.Equiv` records an actual equivalence of ports together with an
equivalence of messages over each translated port.

This is intentionally based on the existing `PFunctor.Equiv` representation
rather than on chart isomorphisms. For the boundary layer, the stronger
structural equivalence is more convenient: the standard coproduct and tensor
coherence facts already live at this level, and packet/query translations can
be recovered from it when needed.
-/
abbrev Equiv (I : Interface.{uA, uB}) (J : Interface.{vA, vB}) :=
  PFunctor.Equiv I J

/--
`QueryHom I J` is the boundary-facing name for `PFunctor.Lens I J`.

A query hom translates continuation-bearing queries from `I` to `J`:

* `toFunA` maps the queried port, and
* `toFunB` reinterprets a response on the translated port back as a response
  on the original port.

In more operational terms, `QueryHom` answers the question:

> if a component wants to query interface `I`, how should that query be
> retargeted to interface `J`, and how should the eventual response be turned
> back into an `I`-response?

So charts are the right notion for concrete packets, while query homs are the
right notion for one-step interactive behavior. This is why the message map in
`QueryHom` goes in the opposite direction from `Hom`: queries move outward, but
their responses must be pulled back. The same underlying representation is
still `PFunctor.Lens`; the new name is only there to make the interaction-level
role of the abstraction immediately legible.
-/
abbrev QueryHom (I : Interface.{uA, uB}) (J : Interface.{vA, vB}) :=
  PFunctor.Lens I J

namespace Hom

/--
The port component of an interface chart.

This is the interaction-facing name for `PFunctor.Chart.toFunA`.
-/
abbrev onPort
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) : I.A → J.A :=
  f.toFunA

/--
The message component of an interface chart.

For each source port `a`, `onMsg` translates a concrete message on `a` into a
message on the translated target port `f.onPort a`.

So `onMsg` moves in the same direction as the packet itself. This is the
interaction-facing name for `PFunctor.Chart.toFunB`.
-/
abbrev onMsg
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) : {a : I.A} → I.B a → J.B (f.onPort a) :=
  fun {a} => f.toFunB a

/-- The identity interface translation. -/
abbrev id (I : Interface.{uA, uB}) : Hom I I :=
  PFunctor.Chart.id I

/--
Compose two interface translations.

`comp g f` first translates packets along `f`, then along `g`.
-/
abbrev comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (g : Hom J K) (f : Hom I J) : Hom I K :=
  PFunctor.Chart.comp g f

/--
Translate one concrete packet along an interface morphism.
-/
def mapPacket
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) : Packet I → Packet J
  | ⟨a, m⟩ => ⟨f.onPort a, f.onMsg m⟩

@[simp]
theorem id_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) :
    comp (id J) f = f :=
  PFunctor.Chart.id_comp f

@[simp]
theorem comp_id
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) :
    comp f (id I) = f :=
  PFunctor.Chart.comp_id f

theorem comp_assoc
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    {L : Interface}
    (h : Hom K L) (g : Hom J K) (f : Hom I J) :
    comp h (comp g f) = comp (comp h g) f :=
  rfl

@[simp]
theorem mapPacket_id
    {I : Interface.{uA, uB}} :
    mapPacket (id I) = fun p => p := by
  funext p
  cases p
  rfl

@[simp]
theorem mapPacket_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (g : Hom J K) (f : Hom I J) :
    mapPacket (comp g f) = mapPacket g ∘ mapPacket f := by
  funext p
  cases p
  rfl

end Hom

namespace QueryHom

/--
The port component of an interface query hom.

This is the interaction-facing name for `PFunctor.Lens.toFunA`.
-/
abbrev onPort
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) : I.A → J.A :=
  f.toFunA

/--
The message-response component of an interface query hom.

For each queried source port `a`, `onMsg` reinterprets a response on the
translated target port `f.onPort a` back as a response on the original port
`a`.

So `onMsg` moves in the opposite direction from the retargeted query: the query
goes out to `J`, and the response is pulled back to `I`. This is the
interaction-facing name for `PFunctor.Lens.toFunB`.
-/
abbrev onMsg
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) : ∀ a : I.A, J.B (f.onPort a) → I.B a :=
  f.toFunB

/-- The identity interface query hom. -/
abbrev id (I : Interface.{uA, uB}) : QueryHom I I :=
  PFunctor.Lens.id I

/--
Compose two interface query homs.

`comp g f` first transports a query along `f`, then transports the resulting
query along `g`.
-/
abbrev comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (g : QueryHom J K) (f : QueryHom I J) : QueryHom I K :=
  PFunctor.Lens.comp g f

/--
Translate one continuation-bearing query along an interface query hom.

If a query asks for a response on interface `I`, then `mapQuery f` retargets
that query to interface `J` and uses the query hom to reinterpret the eventual
response back on the original side.

So `mapQuery` is the query-level companion to `Hom.mapPacket`:

* `Hom.mapPacket` changes traffic that already exists;
* `QueryHom.mapQuery` changes the interface against which a pending
  interaction is asked.
-/
def mapQuery
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {α : Type wA}
    (f : QueryHom I J) : Query I α → Query J α
  | ⟨a, k⟩ => ⟨f.onPort a, fun m => k (f.onMsg a m)⟩

@[simp]
theorem id_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) :
    comp (id J) f = f :=
  PFunctor.Lens.id_comp f

@[simp]
theorem comp_id
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) :
    comp f (id I) = f :=
  PFunctor.Lens.comp_id f

theorem comp_assoc
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    {L : Interface}
    (h : QueryHom K L) (g : QueryHom J K) (f : QueryHom I J) :
    comp h (comp g f) = comp (comp h g) f :=
  rfl

@[simp]
theorem mapQuery_id
    {I : Interface.{uA, uB}}
    {α : Type wA} :
    mapQuery (α := α) (id I) = fun q => q := by
  funext q
  cases q
  rfl

@[simp]
theorem mapQuery_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    {α : Type wA}
    (g : QueryHom J K) (f : QueryHom I J) :
    mapQuery (α := α) (comp g f) =
      mapQuery (α := α) g ∘ mapQuery (α := α) f := by
  funext q
  cases q
  rfl

end QueryHom

/--
The empty interface with no ports and therefore no packets.
-/
abbrev empty : Interface :=
  0

/--
Disjoint sum of interfaces.

A packet on `sum Σ Τ` is either:

* a packet on `Σ`, tagged by `Sum.inl`, or
* a packet on `Τ`, tagged by `Sum.inr`.

This is the structural operation used later for side-by-side composition of
open boundaries.

This is just the ordinary coproduct of polynomial functors. To keep the
representation definitionally simple, both sides share the same message
universe. That is already the regime used by the current open-composition
layer, so no extra universe-lifting machinery is needed here.
-/
abbrev sum (I : Interface.{uA, uB}) (J : Interface.{vA, uB}) :
    Interface.{max uA vA, uB} :=
  I + J

namespace Hom

/--
Combine two interface charts side by side.

The resulting chart acts independently on the left and right summands of the
disjoint-sum interface.
-/
def sum
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    (f₁ : Hom I₁ J₁) (f₂ : Hom I₂ J₂) :
    Hom (Interface.sum I₁ I₂) (Interface.sum J₁ J₂) where
  toFunA := Sum.map f₁.onPort f₂.onPort
  toFunB
    | .inl _ => f₁.onMsg
    | .inr _ => f₂.onMsg

@[simp]
theorem sum_id
    {I₁ : Interface.{uA, uB}}
    {I₂ : Interface.{vA, uB}} :
    sum (id I₁) (id I₂) = id (Interface.sum I₁ I₂) := by
  ext a <;> cases a <;> rfl

theorem sum_comp
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    {K₁ : Interface} {K₂ : Interface}
    (g₁ : Hom J₁ K₁) (f₁ : Hom I₁ J₁)
    (g₂ : Hom J₂ K₂) (f₂ : Hom I₂ J₂) :
    sum (comp g₁ f₁) (comp g₂ f₂) = comp (sum g₁ g₂) (sum f₁ f₂) := by
  ext a <;> cases a <;> rfl

/--
Left inclusion into a disjoint sum of interfaces.

Maps a packet on `I₁` to the left summand of `sum I₁ I₂`.
-/
def inl (I₁ : Interface.{uA, uB}) (I₂ : Interface.{vA, uB}) :
    Hom I₁ (Interface.sum I₁ I₂) where
  toFunA := Sum.inl
  toFunB _ m := m

/--
Right inclusion into a disjoint sum of interfaces.

Maps a packet on `I₂` to the right summand of `sum I₁ I₂`.
-/
def inr (I₁ : Interface.{uA, uB}) (I₂ : Interface.{vA, uB}) :
    Hom I₂ (Interface.sum I₁ I₂) where
  toFunA := Sum.inr
  toFunB _ m := m

@[simp]
theorem mapPacket_inl (I₁ : Interface.{uA, uB}) (I₂ : Interface.{vA, uB})
    (pkt : Packet I₁) :
    mapPacket (inl I₁ I₂) pkt = ⟨Sum.inl pkt.1, pkt.2⟩ := rfl

@[simp]
theorem mapPacket_inr (I₁ : Interface.{uA, uB}) (I₂ : Interface.{vA, uB})
    (pkt : Packet I₂) :
    mapPacket (inr I₁ I₂) pkt = ⟨Sum.inr pkt.1, pkt.2⟩ := rfl

@[simp]
theorem comp_sum_inl
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    (f₁ : Hom I₁ J₁) (f₂ : Hom I₂ J₂) :
    comp (sum f₁ f₂) (inl I₁ I₂) = comp (inl J₁ J₂) f₁ := by
  ext a <;> rfl

@[simp]
theorem comp_sum_inr
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    (f₁ : Hom I₁ J₁) (f₂ : Hom I₂ J₂) :
    comp (sum f₁ f₂) (inr I₁ I₂) = comp (inr J₁ J₂) f₂ := by
  ext a <;> rfl

end Hom

namespace QueryHom

/--
Combine two interface query homs side by side.

The resulting query hom retargets left and right coproduct queries
independently.
-/
abbrev sum
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, vB}} {J₂ : Interface.{wB, vB}}
    (f₁ : QueryHom I₁ J₁) (f₂ : QueryHom I₂ J₂) :
    QueryHom (Interface.sum I₁ I₂) (Interface.sum J₁ J₂) :=
  PFunctor.Lens.sumMap f₁ f₂

@[simp]
theorem sum_id
    {I₁ : Interface.{uA, uB}}
    {I₂ : Interface.{vA, uB}} :
    sum (id I₁) (id I₂) = id (Interface.sum I₁ I₂) := by
  ext a <;> cases a <;> rfl

theorem sum_comp
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, vB}} {J₂ : Interface.{wB, vB}}
    {K₁ : Interface} {K₂ : Interface}
    (g₁ : QueryHom J₁ K₁) (f₁ : QueryHom I₁ J₁)
    (g₂ : QueryHom J₂ K₂) (f₂ : QueryHom I₂ J₂) :
    sum (comp g₁ f₁) (comp g₂ f₂) = comp (sum g₁ g₂) (sum f₁ f₂) := by
  ext a <;> cases a <;> rfl

end QueryHom

namespace Equiv

/--
The forward packet translation carried by an interface equivalence.
-/
abbrev toHom
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (e : Equiv I J) : Hom I J :=
  e.toChart

/--
The inverse packet translation carried by an interface equivalence.
-/
abbrev invHom
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (e : Equiv I J) : Hom J I :=
  e.symm.toChart

/-- The identity interface equivalence. -/
abbrev refl (I : Interface.{uA, uB}) : Equiv I I :=
  PFunctor.Equiv.refl I

/-- Reverse an interface equivalence. -/
abbrev symm
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (e : Equiv I J) : Equiv J I :=
  PFunctor.Equiv.symm e

/--
Compose two interface equivalences.

`trans e₁ e₂` first changes the interface along `e₁`, then along `e₂`.
-/
abbrev trans
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (e₁ : Equiv I J) (e₂ : Equiv J K) : Equiv I K :=
  PFunctor.Equiv.trans e₁ e₂

/--
Interface equivalence is preserved under disjoint sum.
-/
def sumCongr
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    (e₁ : Equiv I₁ J₁) (e₂ : Equiv I₂ J₂) :
    Equiv (Interface.sum I₁ I₂) (Interface.sum J₁ J₂) where
  equivA := _root_.Equiv.sumCongr e₁.equivA e₂.equivA
  equivB
    | .inl a => e₁.equivB a
    | .inr a => e₂.equivB a

/--
The forward packet translation of `sumCongr` is exactly the coproduct of the
forward packet translations on each summand.
-/
@[simp]
theorem toHom_sumCongr
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    (e₁ : Equiv I₁ J₁) (e₂ : Equiv I₂ J₂) :
    (sumCongr e₁ e₂).toHom = Interface.Hom.sum e₁.toHom e₂.toHom := by
  ext a <;> cases a <;> rfl

/-- The empty interface is a left unit for disjoint sum. -/
def emptySum
    (I : Interface.{uA, uB}) :
    Equiv (Interface.sum Interface.empty I) I :=
  PFunctor.Equiv.zeroSum I

/-- The empty interface is a right unit for disjoint sum. -/
def sumEmpty
    (I : Interface.{uA, uB}) :
    Equiv (Interface.sum I Interface.empty) I :=
  PFunctor.Equiv.sumZero I

/-- Disjoint sum of interfaces is commutative up to equivalence. -/
def sumComm
    (I : Interface.{uA, uB}) (J : Interface.{vA, uB}) :
    Equiv (Interface.sum I J) (Interface.sum J I) :=
  PFunctor.Equiv.sumComm I J

/-- Disjoint sum of interfaces is associative up to equivalence. -/
def sumAssoc
    (I : Interface.{uA, uB})
    (J : Interface.{vA, uB})
    (K : Interface.{wA, uB}) :
    Equiv (Interface.sum (Interface.sum I J) K)
      (Interface.sum I (Interface.sum J K)) :=
  PFunctor.Equiv.sumAssoc I J K

end Equiv

/--
Composition product of interfaces (the composition monoidal product on
polynomial functors; see Niu–Spivak 2024).

A position of `comp I J` is a pair of:

* a port `a : I.A` on the outer interface, and
* for each response `m : I.B a` on that port, a port of the inner interface:
  a function `I.B a → J.A`.

A direction at a composed position `⟨a, f⟩` is a dependent pair `⟨u, v⟩`
where `u : I.B a` is a response on port `a` and `v : J.B (f u)` is a
response on the resulting inner port.

This models sequential dependence: one interface's response determines which
port of the next interface is activated.
-/
abbrev comp (I : Interface.{uA, uB}) (J : Interface.{vA, vB}) :
    Interface.{max uA vA uB, max uB vB} :=
  PFunctor.comp I J

/--
The monoidal unit for the composition product.

This is the polynomial functor with one port carrying one message:
`comp I compUnit ≃ I ≃ comp compUnit I`.
-/
abbrev compUnit : Interface :=
  PFunctor.compUnit

namespace QueryHom

/--
Bifunctorial action of query homs on the composition product.

Given query homs `f₁ : QueryHom I₁ J₁` and `f₂ : QueryHom I₂ J₂`, produces
a query hom on the composed interfaces.

There is no corresponding `Hom.compMap` because charts (covariant on both
components) are not functorial for the composition product; the composition
product requires contravariance on B, which only lenses provide.
-/
abbrev compMap
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, vB}}
    {J₁ : Interface.{wA, wB}} {J₂ : Interface}
    (f₁ : QueryHom I₁ J₁) (f₂ : QueryHom I₂ J₂) :
    QueryHom (Interface.comp I₁ I₂) (Interface.comp J₁ J₂) :=
  PFunctor.Lens.compMap f₁ f₂

end QueryHom

namespace Equiv

/-- The composition product is associative up to interface equivalence. -/
abbrev compAssoc
    (I : Interface.{uA, uB})
    (J : Interface.{vA, vB})
    (K : Interface.{wA, wB}) :
    Equiv (Interface.comp (Interface.comp I J) K)
      (Interface.comp I (Interface.comp J K)) :=
  PFunctor.Equiv.compAssoc I J K

/-- `compUnit` is a right unit for composition. -/
abbrev compUnitRight (I : Interface.{uA, uB}) :
    Equiv (Interface.comp I compUnit) I :=
  PFunctor.Equiv.compX I

/-- `compUnit` is a left unit for composition. -/
abbrev compUnitLeft (I : Interface.{uA, uB}) :
    Equiv (Interface.comp compUnit I) I :=
  PFunctor.Equiv.XComp I

end Equiv

end Interface

/--
`PortBoundary` is a directed open boundary for a component or world.

* `In` is the interface of packets accepted from the outside.
* `Out` is the interface of packets emitted to the outside.

The direction matters: later plugging and contextual composition should not
identify incoming and outgoing traffic.
-/
structure PortBoundary where
  In : Interface
  Out : Interface

namespace PortBoundary

/--
The empty open boundary: no inputs and no outputs.
-/
def empty : PortBoundary :=
  ⟨Interface.empty, Interface.empty⟩

/--
Swap the direction of a boundary.

This is the structural operation underlying plugging:
the outputs expected by one side become inputs for the other, and vice versa.
-/
def swap (Δ : PortBoundary) : PortBoundary :=
  ⟨Δ.Out, Δ.In⟩

/--
Side-by-side composition of open boundaries.

Inputs and outputs are combined by disjoint sum, so the resulting boundary
exposes both components in parallel.
-/
def tensor (Δ₁ Δ₂ : PortBoundary) : PortBoundary :=
  ⟨Interface.sum Δ₁.In Δ₂.In, Interface.sum Δ₁.Out Δ₂.Out⟩

/--
`PortBoundary.Hom Δ₁ Δ₂` is a structural adaptation from boundary `Δ₁`
to boundary `Δ₂`.

The variance matches the operational reading:

* inputs are **contravariant**: a consumer of `Δ₂.In` can be fed by packets
  from `Δ₁.In` only if we know how to translate `Δ₂`-inputs back into
  `Δ₁`-inputs;
* outputs are **covariant**: packets produced on `Δ₁.Out` are translated
  forward into `Δ₂.Out`.

This is the boundary-level notion later used for interface adaptation and
structural plugging.
-/
structure Hom (Δ₁ Δ₂ : PortBoundary) where
  onIn : Interface.Hom Δ₂.In Δ₁.In
  onOut : Interface.Hom Δ₁.Out Δ₂.Out

namespace Hom

/--
Two boundary adaptations are equal when their input and output interface maps
are equal.
-/
@[ext]
theorem ext
    {Δ₁ Δ₂ : PortBoundary}
    (f g : Hom Δ₁ Δ₂)
    (hIn : f.onIn = g.onIn)
    (hOut : f.onOut = g.onOut) :
    f = g := by
  cases f
  cases g
  cases hIn
  cases hOut
  rfl

/--
Combine two boundary adaptations side by side.

This is the boundary-level companion to `PortBoundary.tensor`: the left and
right adaptations act independently on the corresponding summands.
-/
def tensor
    {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary}
    (f₁ : Hom Δ₁ Δ₁') (f₂ : Hom Δ₂ Δ₂') :
    Hom (PortBoundary.tensor Δ₁ Δ₂) (PortBoundary.tensor Δ₁' Δ₂') where
  onIn := Interface.Hom.sum f₁.onIn f₂.onIn
  onOut := Interface.Hom.sum f₁.onOut f₂.onOut

/--
Swap the direction of a boundary adaptation.

This is the structural boundary-level counterpart of `PortBoundary.swap`:
incoming and outgoing interface maps exchange roles.
-/
def swap
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    Hom (PortBoundary.swap Δ₂) (PortBoundary.swap Δ₁) where
  onIn := f.onOut
  onOut := f.onIn

/-- The identity boundary adaptation. -/
def id (Δ : PortBoundary) : Hom Δ Δ where
  onIn := Interface.Hom.id Δ.In
  onOut := Interface.Hom.id Δ.Out

/--
Compose two boundary adaptations.

`comp g f` first adapts `Δ₁` to `Δ₂`, then adapts `Δ₂` to `Δ₃`.
-/
def comp
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) : Hom Δ₁ Δ₃ where
  onIn := Interface.Hom.comp f.onIn g.onIn
  onOut := Interface.Hom.comp g.onOut f.onOut

@[simp]
theorem id_comp
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    comp (id Δ₂) f = f := by
  cases f
  simp [comp, id]

@[simp]
theorem comp_id
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    comp f (id Δ₁) = f := by
  cases f
  simp [comp, id]

theorem comp_assoc
    {Δ₁ Δ₂ Δ₃ Δ₄ : PortBoundary}
    (h : Hom Δ₃ Δ₄) (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) :
    comp h (comp g f) = comp (comp h g) f := by
  cases f
  cases g
  cases h
  simp [comp, Interface.Hom.comp_assoc]

@[simp]
theorem tensor_id
    {Δ₁ Δ₂ : PortBoundary} :
    tensor (id Δ₁) (id Δ₂) = id (PortBoundary.tensor Δ₁ Δ₂) := by
  cases Δ₁
  cases Δ₂
  simp [tensor, id, Interface.Hom.sum_id]
  constructor <;> rfl

theorem tensor_comp
    {Δ₁ Δ₂ Δ₃ Δ₄ Δ₁' Δ₂' : PortBoundary}
    (g₁ : Hom Δ₁' Δ₃) (f₁ : Hom Δ₁ Δ₁')
    (g₂ : Hom Δ₂' Δ₄) (f₂ : Hom Δ₂ Δ₂') :
    tensor (comp g₁ f₁) (comp g₂ f₂) =
      comp (tensor g₁ g₂) (tensor f₁ f₂) := by
  cases f₁
  cases f₂
  cases g₁
  cases g₂
  simp only [tensor, comp, Interface.Hom.sum_comp]
  rfl

@[simp]
theorem swap_id
    {Δ : PortBoundary} :
    swap (id Δ) = id (PortBoundary.swap Δ) := by
  cases Δ
  rfl

theorem swap_comp
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) :
    swap (comp g f) = comp (swap f) (swap g) := by
  cases f
  cases g
  rfl

@[simp]
theorem swap_swap
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    swap (swap f) = f := by
  cases f
  rfl

end Hom

/--
`PortBoundary.Equiv Δ₁ Δ₂` is the variance-aware notion of boundary
isomorphism.

It is described directly in terms of interface equivalences:

* `onIn` is an equivalence from `Δ₂.In` to `Δ₁.In`, reflecting the
  contravariant role of inputs;
* `onOut` is an equivalence from `Δ₁.Out` to `Δ₂.Out`, reflecting the
  covariant role of outputs.

This is the right structure for expressing coherence laws of open composition:
the exposed boundary may change shape, but only up to a canonical directed
isomorphism.
-/
structure Equiv (Δ₁ Δ₂ : PortBoundary) where
  onIn : Interface.Equiv Δ₂.In Δ₁.In
  onOut : Interface.Equiv Δ₁.Out Δ₂.Out

namespace Equiv

/--
The forward boundary adaptation carried by a boundary equivalence.
-/
abbrev toHom
    {Δ₁ Δ₂ : PortBoundary}
    (e : Equiv Δ₁ Δ₂) : Hom Δ₁ Δ₂ where
  onIn := e.onIn.toHom
  onOut := e.onOut.toHom

/--
The inverse boundary adaptation carried by a boundary equivalence.
-/
abbrev invHom
    {Δ₁ Δ₂ : PortBoundary}
    (e : Equiv Δ₁ Δ₂) : Hom Δ₂ Δ₁ where
  onIn := e.onIn.invHom
  onOut := e.onOut.invHom

/-- The identity boundary equivalence. -/
abbrev refl (Δ : PortBoundary) : Equiv Δ Δ where
  onIn := Interface.Equiv.refl Δ.In
  onOut := Interface.Equiv.refl Δ.Out

/-- Reverse a boundary equivalence. -/
abbrev symm
    {Δ₁ Δ₂ : PortBoundary}
    (e : Equiv Δ₁ Δ₂) : Equiv Δ₂ Δ₁ where
  onIn := e.onIn.symm
  onOut := e.onOut.symm

/--
Compose two boundary equivalences.

`trans e₁ e₂` first changes the exposed boundary along `e₁`, then along `e₂`.
-/
abbrev trans
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (e₁ : Equiv Δ₁ Δ₂) (e₂ : Equiv Δ₂ Δ₃) : Equiv Δ₁ Δ₃ where
  onIn := Interface.Equiv.trans e₂.onIn e₁.onIn
  onOut := Interface.Equiv.trans e₁.onOut e₂.onOut

/--
Boundary equivalence is preserved under tensor.
-/
def tensorCongr
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
    (e₁ : Equiv Δ₁ Δ₁') (e₂ : Equiv Δ₂ Δ₂') :
    Equiv (PortBoundary.tensor Δ₁ Δ₂) (PortBoundary.tensor Δ₁' Δ₂') where
  onIn := Interface.Equiv.sumCongr e₁.onIn e₂.onIn
  onOut := Interface.Equiv.sumCongr e₁.onOut e₂.onOut

/--
The forward boundary adaptation of `tensorCongr` is exactly the tensor of the
forward boundary adaptations on each factor.
-/
@[simp]
theorem toHom_tensorCongr
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
    (e₁ : Equiv Δ₁ Δ₁') (e₂ : Equiv Δ₂ Δ₂') :
    (tensorCongr e₁ e₂).toHom = PortBoundary.Hom.tensor e₁.toHom e₂.toHom := by
  apply PortBoundary.Hom.ext
  · exact Interface.Equiv.toHom_sumCongr e₁.onIn e₂.onIn
  · exact Interface.Equiv.toHom_sumCongr e₁.onOut e₂.onOut

/--
Swapping the direction of boundaries preserves equivalence.
-/
abbrev swapCongr
    {Δ₁ Δ₂ : PortBoundary}
    (e : Equiv Δ₁ Δ₂) :
    Equiv (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂) where
  onIn := e.onOut.symm
  onOut := e.onIn.symm

/--
The forward boundary adaptation of `swapCongr` is exactly the swapped forward
inverse boundary adaptation.
-/
@[simp]
theorem toHom_swapCongr
    {Δ₁ Δ₂ : PortBoundary}
    (e : Equiv Δ₁ Δ₂) :
    (swapCongr e).toHom = PortBoundary.Hom.swap e.invHom := by
  rfl


/-- The empty boundary is a left tensor unit. -/
def tensorEmptyLeft
    (Δ : PortBoundary) :
    Equiv (PortBoundary.tensor PortBoundary.empty Δ) Δ where
  onIn := (Interface.Equiv.emptySum Δ.In).symm
  onOut := Interface.Equiv.emptySum Δ.Out

/-- The empty boundary is a right tensor unit. -/
def tensorEmptyRight
    (Δ : PortBoundary) :
    Equiv (PortBoundary.tensor Δ PortBoundary.empty) Δ where
  onIn := (Interface.Equiv.sumEmpty Δ.In).symm
  onOut := Interface.Equiv.sumEmpty Δ.Out

/-- Tensor of boundaries is symmetric up to equivalence. -/
def tensorComm
    (Δ₁ Δ₂ : PortBoundary) :
    Equiv (PortBoundary.tensor Δ₁ Δ₂) (PortBoundary.tensor Δ₂ Δ₁) where
  onIn := Interface.Equiv.sumComm Δ₂.In Δ₁.In
  onOut := Interface.Equiv.sumComm Δ₁.Out Δ₂.Out

/-- Tensor of boundaries is associative up to equivalence. -/
def tensorAssoc
    (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    Equiv (PortBoundary.tensor (PortBoundary.tensor Δ₁ Δ₂) Δ₃)
      (PortBoundary.tensor Δ₁ (PortBoundary.tensor Δ₂ Δ₃)) where
  onIn := (Interface.Equiv.sumAssoc Δ₁.In Δ₂.In Δ₃.In).symm
  onOut := Interface.Equiv.sumAssoc Δ₁.Out Δ₂.Out Δ₃.Out

/-- Swapping twice yields the original boundary, up to equivalence. -/
abbrev swapSwap
    (Δ : PortBoundary) :
    Equiv (PortBoundary.swap (PortBoundary.swap Δ)) Δ :=
  refl Δ

private theorem eqRec_id_apply_codomain
    {α : Sort*} {β : α → Sort*} {a₀ a₁ : α}
    (h : a₀ = a₁) (x : β a₀) :
    Eq.rec (motive := fun x _ => β a₀ → β x) id h x =
      _root_.cast (congrArg β h) x := by
  subst h; rfl

private theorem chart_comp_symm_eq_id
    {P : PFunctor} {Q : PFunctor} (e : PFunctor.Equiv P Q) :
    PFunctor.Chart.comp e.symm.toChart e.toChart =
      PFunctor.Chart.id P := by
  refine PFunctor.Chart.ext _ _
    (fun a => e.equivA.symm_apply_apply a) (fun a => ?_)
  funext b
  simp only [PFunctor.Chart.comp, PFunctor.Chart.id,
    PFunctor.Equiv.toChart, Function.comp_apply]
  change (((_root_.Equiv.cast _).trans
    (e.equivB (e.equivA.symm (e.equivA a))).symm)
    (e.equivB a b)) = _
  simp only [_root_.Equiv.trans_apply]
  trans _root_.cast
    (congrArg P.B (e.equivA.symm_apply_apply a).symm) b
  · exact PFunctor.Equiv.equivB_symm_apply_of_eq e
      (e.equivA.apply_symm_apply (e.equivA a)) b
  · exact (eqRec_id_apply_codomain
      (e.equivA.symm_apply_apply a).symm b).symm

private theorem chart_comp_inv_eq_id
    {P : PFunctor} {Q : PFunctor} (e : PFunctor.Equiv P Q) :
    PFunctor.Chart.comp e.toChart e.symm.toChart =
      PFunctor.Chart.id Q := by
  refine PFunctor.Chart.ext _ _
    (fun a => e.equivA.apply_symm_apply a) (fun a => ?_)
  funext b
  simp only [PFunctor.Chart.comp, PFunctor.Chart.id,
    PFunctor.Equiv.toChart, Function.comp_apply]
  change ((e.equivB (e.equivA.symm a)))
    (((_root_.Equiv.cast _).trans
      (e.equivB (e.equivA.symm a)).symm) b) = _
  simp only [_root_.Equiv.trans_apply,
    _root_.Equiv.apply_symm_apply]
  exact (eqRec_id_apply_codomain
    (e.equivA.apply_symm_apply a).symm b).symm

@[simp]
theorem symm_toHom_comp_toHom
    {Δ₁ Δ₂ : PortBoundary}
    (e : PortBoundary.Equiv Δ₁ Δ₂) :
    Hom.comp e.symm.toHom e.toHom = Hom.id Δ₁ := by
  apply Hom.ext
  · exact chart_comp_inv_eq_id e.onIn
  · exact chart_comp_symm_eq_id e.onOut

@[simp]
theorem toHom_comp_symm_toHom
    {Δ₁ Δ₂ : PortBoundary}
    (e : PortBoundary.Equiv Δ₁ Δ₂) :
    Hom.comp e.toHom e.symm.toHom = Hom.id Δ₂ := by
  apply Hom.ext
  · exact chart_comp_symm_eq_id e.onIn
  · exact chart_comp_inv_eq_id e.onOut

@[simp]
theorem tensorComm_comp_tensorComm
    (Δ₁ Δ₂ : PortBoundary) :
    Hom.comp (tensorComm Δ₂ Δ₁).toHom (tensorComm Δ₁ Δ₂).toHom =
    Hom.id _ := by
  apply Hom.ext
  all_goals {
    refine PFunctor.Chart.ext _ _ (fun a => ?_) (fun a => ?_)
    · cases a <;> rfl
    · funext b; cases a <;> rfl
  }

end Equiv

@[simp]
theorem swap_swap (Δ : PortBoundary) : Δ.swap.swap = Δ := by
  cases Δ
  rfl

end PortBoundary

end UC
end Interaction
