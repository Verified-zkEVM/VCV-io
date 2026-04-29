/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.SimpAttr
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.StateSeparating

/-!
# Oracle interfaces and plain states for the stateful Fiat-Shamir CMA proof

This file contains the oracle interfaces and direct product-state shapes used
by the `QueryImpl.Stateful` Fiat-Shamir CMA games. The games store their private
data in ordinary product types.

The `fs_simp` simp attribute used to tag handler definitions, frames, lenses,
and adversary wrappers throughout the stateful FS-CMA development is declared
in `Stateful/SimpAttr.lean` and imported above.
-/

open OracleSpec

namespace FiatShamir.Stateful

/-! ## Oracle specs -/

/-- Named query constructors for the source CMA adversary interface. -/
inductive CmaSourceQuery (M Commit : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Signing query. -/
  | sign (m : M)

/-- Named query constructors for the CMA adversary's oracle view. -/
inductive CmaQuery (M Commit : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Signing query. -/
  | sign (m : M)
  /-- Public-key query. -/
  | pk

/-- Named query constructors for the public, non-signing portion of the CMA
interface. -/
inductive CmaPublicQuery (M Commit : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Public-key query. -/
  | pk

/-- Named query constructors for the NMA interface used internally by the
CMA-to-NMA reduction. -/
inductive NmaQuery (M Commit Chal : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Public-key query. -/
  | pk
  /-- Programmable-random-oracle query. -/
  | prog (mch : M × Commit × Chal)

/-- Random-oracle interface for the Fiat-Shamir transform. -/
@[reducible] def roSpec (M Commit Chal : Type) : OracleSpec (M × Commit) :=
  (M × Commit) →ₒ Chal

/-- Signing-oracle interface presented to the CMA adversary. -/
@[reducible] def signSpec (M Commit Resp : Type) : OracleSpec M :=
  M →ₒ (Commit × Resp)

/-- Public-key oracle interface: a single `GetPK` query returning the
challenger's public key. -/
@[reducible] def pkSpec (Stmt : Type) : OracleSpec Unit :=
  Unit →ₒ Stmt

/-- Programming interface for the programmable random oracle. -/
@[reducible] def progSpec (M Commit Chal : Type) : OracleSpec (M × Commit × Chal) :=
  (M × Commit × Chal) →ₒ Unit

/-- Source CMA adversary interface: uniform sampling, RO, and signing. -/
@[reducible] def cmaSourceSpec (M Commit Chal Resp : Type) :
    OracleSpec (CmaSourceQuery M Commit) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .sign _ => Commit × Resp

/-- The CMA adversary's complete oracle view: uniform sampling, RO, signing,
and public-key oracles. -/
@[reducible] def cmaSpec (M Commit Chal Resp Stmt : Type) :
    OracleSpec (CmaQuery M Commit) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .sign _ => Commit × Resp
    | .pk => Stmt

/-- The non-signing portion of the CMA adversary's oracle view. -/
@[reducible] def cmaPublicSpec (M Commit Chal Stmt : Type) :
    OracleSpec (CmaPublicQuery M Commit) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .pk => Stmt

/-- The NMA-game oracle interface used internally by the CMA-to-NMA reduction.
Includes uniform sampling, RO, programmable RO, and public-key queries. -/
@[reducible] def nmaSpec (M Commit Chal Stmt : Type) :
    OracleSpec (NmaQuery M Commit Chal) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .pk => Stmt
    | .prog _ => Unit

/-- Route named CMA queries to the public-forwarding component or the signing
component of the CMA-to-NMA reduction. -/
def cmaRoute (M Commit Chal Resp Stmt : Type) :
    QueryImpl.Stateful.ExportRouteEquiv
      (cmaSpec M Commit Chal Resp Stmt)
      (cmaPublicSpec M Commit Chal Stmt)
      (signSpec M Commit Resp) where
  route
    | .unif n => .inl ⟨.unif n, Equiv.refl _⟩
    | .ro mc => .inl ⟨.ro mc, Equiv.refl _⟩
    | .sign m => .inr ⟨m, Equiv.refl _⟩
    | .pk => .inl ⟨.pk, Equiv.refl _⟩
  targetEquiv := {
    toFun
      | .unif n => Sum.inl (CmaPublicQuery.unif n)
      | .ro mc => Sum.inl (CmaPublicQuery.ro mc)
      | .sign m => Sum.inr m
      | .pk => Sum.inl CmaPublicQuery.pk
    invFun
      | Sum.inl (CmaPublicQuery.unif n) => CmaQuery.unif n
      | Sum.inl (CmaPublicQuery.ro mc) => CmaQuery.ro mc
      | Sum.inl CmaPublicQuery.pk => CmaQuery.pk
      | Sum.inr m => CmaQuery.sign m
    left_inv := by
      intro t
      cases t <;> rfl
    right_inv := by
      intro t
      rcases t with (t | m)
      · cases t <;> rfl
      · rfl
  }
  target_eq := by
    intro t
    rcases t with (_ | _) | _ <;> rfl

instance subSpec_unif_nmaSpec (M Commit Chal Stmt : Type) :
    unifSpec ⊂ₒ nmaSpec M Commit Chal Stmt where
  monadLift q := ⟨.unif q.input, q.cont⟩
  onQuery n := .unif n
  onResponse _ := id
  liftM_eq_lift _ := rfl

instance lawfulSubSpec_unif_nmaSpec (M Commit Chal Stmt : Type) :
    unifSpec ˡ⊂ₒ nmaSpec M Commit Chal Stmt where
  onResponse_bijective _ := Function.bijective_id

instance subSpec_unif_cmaSpec (M Commit Chal Resp Stmt : Type) :
    unifSpec ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  monadLift q := ⟨.unif q.input, q.cont⟩
  onQuery n := .unif n
  onResponse _ := id

instance lawfulSubSpec_unif_cmaSpec (M Commit Chal Resp Stmt : Type) :
    unifSpec ˡ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  onResponse_bijective _ := Function.bijective_id

instance subSpec_ro_cmaSpec (M Commit Chal Resp Stmt : Type) :
    roSpec M Commit Chal ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  monadLift q := ⟨.ro q.input, q.cont⟩
  onQuery mc := .ro mc
  onResponse _ := id

instance lawfulSubSpec_ro_cmaSpec (M Commit Chal Resp Stmt : Type) :
    roSpec M Commit Chal ˡ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  onResponse_bijective _ := Function.bijective_id

instance subSpec_sign_cmaSpec (M Commit Chal Resp Stmt : Type) :
    signSpec M Commit Resp ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  monadLift q := ⟨.sign q.input, q.cont⟩
  onQuery m := .sign m
  onResponse _ := id

instance lawfulSubSpec_sign_cmaSpec (M Commit Chal Resp Stmt : Type) :
    signSpec M Commit Resp ˡ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  onResponse_bijective _ := Function.bijective_id

instance subSpec_pk_cmaSpec (M Commit Chal Resp Stmt : Type) :
    pkSpec Stmt ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  monadLift
    | ⟨(), f⟩ => ⟨.pk, f⟩
  onQuery _ := .pk
  onResponse _ := id

instance lawfulSubSpec_pk_cmaSpec (M Commit Chal Resp Stmt : Type) :
    pkSpec Stmt ˡ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  onResponse_bijective _ := Function.bijective_id

/-- The Fiat-Shamir public random-oracle interface embeds into the named CMA
interface by routing uniform and random-oracle queries to their named
constructors. -/
instance subSpec_fsRo_cmaSpec (M Commit Chal Resp Stmt : Type) :
    (unifSpec + roSpec M Commit Chal) ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  monadLift
    | ⟨.inl n, f⟩ => ⟨.unif n, f⟩
    | ⟨.inr mc, f⟩ => ⟨.ro mc, f⟩
  onQuery
    | .inl n => .unif n
    | .inr mc => .ro mc
  onResponse
    | .inl _ => id
    | .inr _ => id
  liftM_eq_lift q := by
    rcases q with ⟨_ | _, _⟩ <;> rfl

instance lawfulSubSpec_fsRo_cmaSpec (M Commit Chal Resp Stmt : Type) :
    (unifSpec + roSpec M Commit Chal) ˡ⊂ₒ cmaSpec M Commit Chal Resp Stmt where
  onResponse_bijective
    | .inl _ => Function.bijective_id
    | .inr _ => Function.bijective_id

/-- The source CMA adversary interface embeds into the named CMA interface. -/
instance subSpec_sourceCma_cmaSpec (M Commit Chal Resp Stmt : Type) :
    (unifSpec + roSpec M Commit Chal + signSpec M Commit Resp) ⊂ₒ
      cmaSpec M Commit Chal Resp Stmt where
  monadLift
    | ⟨.inl (.inl n), f⟩ => ⟨.unif n, f⟩
    | ⟨.inl (.inr mc), f⟩ => ⟨.ro mc, f⟩
    | ⟨.inr m, f⟩ => ⟨.sign m, f⟩
  onQuery
    | .inl (.inl n) => .unif n
    | .inl (.inr mc) => .ro mc
    | .inr m => .sign m
  onResponse
    | .inl (.inl _) => id
    | .inl (.inr _) => id
    | .inr _ => id
  liftM_eq_lift q := by
    rcases q with ⟨(_ | _) | _, _⟩ <;> rfl

instance lawfulSubSpec_sourceCma_cmaSpec (M Commit Chal Resp Stmt : Type) :
    (unifSpec + roSpec M Commit Chal + signSpec M Commit Resp) ˡ⊂ₒ
      cmaSpec M Commit Chal Resp Stmt where
  onResponse_bijective
    | .inl (.inl _) => Function.bijective_id
    | .inl (.inr _) => Function.bijective_id
    | .inr _ => Function.bijective_id

/-! ## Plain state shapes -/

/-- Random-oracle cache state. -/
abbrev RoCache (M Commit Chal : Type) :=
  (roSpec M Commit Chal).QueryCache

/-- Outer CMA-to-NMA state: the signed-message log. -/
abbrev OuterState (M : Type) :=
  List M

/-- Inner NMA state: RO cache, optional keypair, and bad flag. -/
abbrev NmaState (M Commit Chal Stmt Wit : Type) :=
  RoCache M Commit Chal × Option (Stmt × Wit) × Bool

/-- Direct CMA state without the bad flag: signed log, RO cache, keypair. -/
abbrev CmaData (M Commit Chal Stmt Wit : Type) :=
  OuterState M × RoCache M Commit Chal × Option (Stmt × Wit)

/-- Direct CMA state with the bad flag as the final component. -/
abbrev CmaState (M Commit Chal Stmt Wit : Type) :=
  CmaData M Commit Chal Stmt Wit × Bool

/-- Initial NMA state: empty RO cache, no keypair, bad unset. -/
@[reducible] def nmaInit (M Commit Chal Stmt Wit : Type) :
    NmaState M Commit Chal Stmt Wit :=
  (∅, none, false)

/-- Initial CMA state: empty signed log, empty RO cache, no keypair, bad unset. -/
@[reducible] def cmaInit (M Commit Chal Stmt Wit : Type) :
    CmaState M Commit Chal Stmt Wit :=
  (([], ∅, none), false)

/-! ## Frame for linking CMA-to-NMA over direct CMA state -/

/-- Lens selecting the signed-message log from direct CMA state. -/
@[fs_simp] def cmaOuterLens (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State (CmaState M Commit Chal Stmt Wit) (OuterState M) :=
  PFunctor.Lens.State.mk (fun s => s.1.1)
    (fun log s => ((log, s.1.2.1, s.1.2.2), s.2))

/-- Lens selecting the NMA state from direct CMA state. -/
@[fs_simp] def cmaNmaLens (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State (CmaState M Commit Chal Stmt Wit)
      (NmaState M Commit Chal Stmt Wit) :=
  PFunctor.Lens.State.mk (fun s => (s.1.2.1, s.1.2.2, s.2))
    (fun inner s => ((s.1.1, inner.1, inner.2.1), inner.2.2))

instance cmaOuterLens_isVeryWellBehaved (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State.IsVeryWellBehaved
      (cmaOuterLens M Commit Chal Stmt Wit) where
  get_put := by intro s log; rfl
  put_get := by intro s; rcases s with ⟨⟨log, cache, kp⟩, bad⟩; rfl
  put_put := by intro s log₁ log₂; rfl

instance cmaNmaLens_isVeryWellBehaved (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State.IsVeryWellBehaved
      (cmaNmaLens M Commit Chal Stmt Wit) where
  get_put := by
    intro s inner
    rcases inner with ⟨cache, kp, bad⟩
    rfl
  put_get := by intro s; rcases s with ⟨⟨log, cache, kp⟩, bad⟩; rfl
  put_put := by
    intro s inner₁ inner₂
    rcases inner₁ with ⟨cache₁, kp₁, bad₁⟩
    rcases inner₂ with ⟨cache₂, kp₂, bad₂⟩
    rfl

instance cmaOuterLens_cmaNmaLens_isSeparated (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State.IsSeparated
      (cmaOuterLens M Commit Chal Stmt Wit)
      (cmaNmaLens M Commit Chal Stmt Wit) where
  left_get_put_right := by
    intro s inner
    rcases s with ⟨⟨log, cache, kp⟩, bad⟩
    rcases inner with ⟨cache', kp', bad'⟩
    rfl
  right_get_put_left := by
    intro s log
    rcases s with ⟨⟨log₀, cache, kp⟩, bad⟩
    rfl
  put_comm := by
    intro s log inner
    rcases s with ⟨⟨log₀, cache, kp⟩, bad⟩
    rcases inner with ⟨cache', kp', bad'⟩
    rfl

/-- The direct CMA frame used by `cmaToNma.linkWith nma`. -/
@[fs_simp] def cmaFrame (M Commit Chal Stmt Wit : Type) :
    QueryImpl.Stateful.Frame (CmaState M Commit Chal Stmt Wit)
      (OuterState M) (NmaState M Commit Chal Stmt Wit) where
  left := cmaOuterLens M Commit Chal Stmt Wit
  right := cmaNmaLens M Commit Chal Stmt Wit

/-! ## Frame for routing the CMA-to-NMA reduction -/

/-- Trivial lens into a `PUnit` component. -/
@[fs_simp] def unitLens (σ : Type) : PFunctor.Lens.State σ PUnit :=
  PFunctor.Lens.State.mk (fun _ => PUnit.unit) (fun _ s => s)

instance unitLens_isVeryWellBehaved (σ : Type) :
    PFunctor.Lens.State.IsVeryWellBehaved (unitLens σ) where
  get_put := by intro _ _; rfl
  put_get := by intro _; rfl
  put_put := by intro _ _ _; rfl

instance unitLens_id_isSeparated (σ : Type) :
    PFunctor.Lens.State.IsSeparated (unitLens σ) (PFunctor.Lens.State.id σ) where
  left_get_put_right := by intro _ _; rfl
  right_get_put_left := by intro _ _; rfl
  put_comm := by intro _ _ _; rfl

/-- Frame used to compose the stateless forwarding part of `cmaToNma` with the
stateful signing simulator while keeping only the signing log as state. -/
@[fs_simp] def cmaToNmaFrame (M : Type) :
    QueryImpl.Stateful.Frame (OuterState M) PUnit (OuterState M) where
  left := unitLens (OuterState M)
  right := PFunctor.Lens.State.id (OuterState M)

end FiatShamir.Stateful
