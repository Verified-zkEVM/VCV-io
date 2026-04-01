/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.AsymmEncAlg.Defs

/-!
# KEM-DEM Composition

This file defines a lightweight keyed DEM interface and shows that composing a perfectly
correct KEM with a perfectly correct keyed DEM yields a perfectly correct asymmetric
encryption scheme at the monadic probability level.
-/

open OracleSpec OracleComp ENNReal

universe u

/-- A keyed DEM with message space `M` and ciphertext space `C`. -/
structure KeyedDEM (K M C : Type) where
  encrypt : K → M → C
  decrypt : K → C → Option M

namespace KeyedDEM

variable {K M C : Type}

/-- A keyed DEM is perfectly correct when decrypting an encryption always recovers the message. -/
def PerfectlyCorrect (dem : KeyedDEM K M C) : Prop :=
  ∀ k msg, dem.decrypt k (dem.encrypt k msg) = some msg

end KeyedDEM

variable {m : Type → Type u} {K PK SK M C_kem C_dem : Type}

/-- Compose a KEM with a keyed DEM to obtain an asymmetric encryption scheme. -/
def composeWithDEM [Monad m]
    (kem : KEMScheme m K PK SK C_kem) (dem : KeyedDEM K M C_dem) :
    AsymmEncAlg m M PK SK (C_kem × C_dem) where
  keygen := kem.keygen
  encrypt := fun pk msg => do
    let (c, k) ← kem.encaps pk
    return (c, dem.encrypt k msg)
  decrypt := fun sk ⟨c, ct⟩ => do
    let kOpt ← kem.decaps sk c
    match kOpt with
    | some k => return (dem.decrypt k ct)
    | none => return none
  __ := kem.toExecutionMethod

/-- From KEM correctness at the monadic probability level, every reachable decapsulation of an
honest ciphertext returns the encapsulated key. -/
private lemma kem_decaps_mem_support [Monad m] [DecidableEq K] [HasEvalSPMF m]
    {kem : KEMScheme m K PK SK C_kem}
    (hkem : Pr[=true | kem.CorrectExp] = 1)
    {pk : PK} {sk : SK} (hks : (pk, sk) ∈ support kem.keygen)
    {c : C_kem} {k : K} (hck : (c, k) ∈ support (kem.encaps pk))
    {kOpt : Option K} (hkOpt : kOpt ∈ support (kem.decaps sk c)) :
    kOpt = some k := by
  have hsup : support kem.CorrectExp = {true} :=
    (probOutput_eq_one_iff (mx := kem.CorrectExp) (x := true)).mp hkem |>.2
  rw [KEMScheme.CorrectExp] at hsup
  have : decide (kOpt = some k) ∈ ({true} : Set Bool) := by
    rw [← hsup]
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      decide_eq_decide, exists_prop, Prod.exists]
    exact ⟨pk, sk, hks, c, k, hck, kOpt, hkOpt, Iff.rfl⟩
  simpa using this

/-- If a KEM and keyed DEM are perfectly correct, then their composition is perfectly correct at
the monadic probability level. We work directly with `Pr` rather than the abstract `exec`
interface, since the proof needs support-level facts about intermediate computations. -/
theorem perfectlyCorrect_composeWithDEM [Monad m] [LawfulMonad m]
    [DecidableEq M] [DecidableEq K] [HasEvalSPMF m]
    {kem : KEMScheme m K PK SK C_kem} {dem : KeyedDEM K M C_dem}
    (hkem : Pr[=true | kem.CorrectExp] = 1)
    (hdem : dem.PerfectlyCorrect) :
    ∀ msg, Pr[=true | (composeWithDEM kem dem).CorrectExp msg] = 1 := by
  intro msg
  simp only [AsymmEncAlg.CorrectExp, composeWithDEM]
  rw [← hkem]
  unfold KEMScheme.CorrectExp
  simp only [bind_assoc]
  apply probOutput_bind_congr
  intro ⟨pk, sk⟩ hks
  apply probOutput_bind_congr
  intro ⟨c, k⟩ hck
  simp only [pure_bind]
  apply probOutput_bind_congr
  intro kOpt hkOpt
  have hkEq := kem_decaps_mem_support hkem hks hck hkOpt
  subst hkEq
  simp [hdem k msg]
