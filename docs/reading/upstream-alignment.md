# Upstream alignment survey

A ledger of VCVio's general-purpose machinery and tooling against what Lean core, Std,
Batteries, Mathlib, cslib, and PolyFun already provide, with a verdict for each entry:
**adopt** what upstream owns, **keep** what is genuinely VCVio's, **upstream** what belongs
elsewhere (recorded only; upstream PRs are a separate effort), and **track** what is on its
way to core or blocked on a design decision.

Companion files: [`probability-semantics-landscape.md`](probability-semantics-landscape.md)
(§19–20 are the probability-specific evidence ledger), PolyFun's
`docs/reading/upstream-alignment.md` (the same survey for the polynomial-functor layer,
whose `corrections.md` items 3–5 name VCVio-side duplications recorded below).

## Why this file exists

VCVio keeps discovering after the fact that a dependency already provides something it
hand-rolled, or that its tooling lags what Lake and sibling projects now do natively. The
cost is not the deleted code; it is the design time spent rediscovering an interface and the
review time spent on proofs Mathlib already has. This file is the periodic check against
that drift, and — following the maintainer's priority — a broad reading of the adjacent
Mathlib areas to find where idioms differ and what could be integrated more aggressively (the
"Mathlib reading" section and the integration queue). The rule it encodes: **VCVio owns oracle computations, their probabilistic
semantics, the program logic over them, and the cryptographic games and reductions — and as
little else as it can get away with.**

## Method, and how to repeat it

Every claim below was checked against source on disk, not recalled. A name is a
hypothesis; the declaration in the pinned tree is the evidence. An *absence* claim names the
search that came back empty.

| Tree | Revision surveyed | How |
|---|---|---|
| VCVio | `main` at `31ec290a` (2026-09-02) | worktree; every local row re-grepped there |
| Lean core / Std | `v4.33.1` pin | both toolchains are installed locally; `diff -rq` over their `src/lean` trees reports no differing `.lean` file, so citations use the `v4.33.0` tree; the release notes for 4.31–4.34 were read for the *track* rows |
| Mathlib | `v4.33.1` pin, read from the `v4.33.0` checkout | `git diff --stat v4.33.0 v4.33.1` touches only `lean-toolchain` (PolyFun survey) |
| Batteries | `4488d40d0` | checkout under `.lake/packages` |
| cslib | `v4.33.1` (`98e395a7`) on `main`, read from the `v4.33.0` (`3951377e`) checkout | inherited through PolyFun; `gh api repos/leanprover/cslib/compare/3951377e...98e395a7` lists only `lake-manifest.json`, `lakefile.toml`, `lean-toolchain`, so every `.lean` file cited is identical at both pins |
| PolyFun | `c0c92369` (commit pin) | checkout `9442600` plus the GitHub API for the pin |
| loom2 | `2f65f311` (2026-07-15) | checkout; upstream last commit 2026-04-19 |

Traps recorded by PolyFun and confirmed here: the newest local toolchain directory is not
necessarily newer than the pin (check `bin/lean --version`); anything found on `master` but
absent from the `v4.34.0-rc2` tag ships in v4.35, so a v4.34 bump buys none of it; and an
instance-providing module can be load-bearing with zero textual references, so "unused"
needs an instance-synthesis check, not a grep.

## Ledger

### Adopt — upstream owns it, VCVio duplicates it

| VCVio | Upstream | At the pin? | Status |
|---|---|---|---|
| `ToMathlib/Combinatorics/FinPairs.lean` (whole file; `Finset.card_filter_fst_lt_snd` :95) | `Fintype.card_product_filter_lt`, `Mathlib/Data/Fintype/Prod.lean:64`; `Finset.card_product_filter_lt`, `Mathlib/Data/Finset/Prod.lean:370` | yes | **done** (this PR) — one consumer, `VCVio/OracleComp/QueryTracking/Birthday.lean:263`; the whole file goes |
| `ToMathlib/General.lean:430` `instance Fintype (BitVec n)` | `FinEnum (BitVec n)`, `Mathlib/Data/FinEnum.lean:299`, with the priority-100 `FinEnum → Fintype` instance at `:194` | yes | **done** (this PR): in the VCVio closure `#synth Fintype (BitVec 3)` returns the local instance while `SampleableType (BitVec 3)` already goes through `FinEnum`; two non-defeq `Fintype`s coexist today |
| `ToMathlib/General.lean:419` `BitVec.toFin_bijective` | `BitVec.toFin_injective`, `Mathlib/Data/BitVec.lean:55`; `BitVec.equivFin`, `:107` | yes | **done** (this PR) — 0 consumers |
| `ToMathlib/General.lean:156,165` `tprod_ite_eq_apply`, `'` (+ `tsum` twins) | `tprod_ite_eq`, `tprod_ite_eq'`, `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:510,518` (both `@[simp]`, `to_additive`) | yes | **done** (this PR) — identical statements, 0 consumers |
| `ToMathlib/General.lean:280` `Finset.image_const_univ` | `Finset.image_const`, `Mathlib/Data/Finset/Image.lean:568` (`Finset.image_const univ_nonempty b`) | yes | **done** (this PR) — 0 named consumers; it is `@[simp]`, so deletion is guarded by a full build |
| `ToMathlib/MeasureTheory/DiscreteInstances.lean:39` `BitVec.instFinite` | `FinEnum → Fintype → Finite` | yes | **keep** — the `Finite` instance is `Prop`-valued and lets the module stand alone without importing `Mathlib.Data.FinEnum`; only its docstring changed (this PR) |
| `ToMathlib/Control/Monad/Commutative.lean:35` `Monad.Commutative`, `CommutativeAt` :26, `Set.monadComm` :196, the `Id`/`Option`/`Except`/`ReaderT` instances | `CommApplicative`, `Mathlib/Control/Basic.lean:206`; `instance : CommApplicative Set`, `Mathlib/Data/Set/Functor.lean:88` | yes | **done** (this PR) — 0 consumers outside the file; for a `LawfulMonad`, `bind_comm` follows from `CommApplicative.commutative_prod` via `seq_eq_bind_map`, and the converse constructs `CommApplicative` (both compiled during the survey). Mathlib has **no** `CommApplicative Option`/`Id`/`Except`/`ReaderT` instances at the pin (`grep instance.*CommApplicative` → `Finset`, `Set`, `Applicative.lean:74`, `FreeAbelianGroup`, `Filter`), so those four become *upstream* rows |
| `ToMathlib/Control/WriterT.lean:130` `run_seqLeft'` | local `run_seqLeft` :83 | — | **done** (this PR) — verbatim duplicate inside the same file, 0 consumers |
| `ToMathlib/Control/Monad/Ordered.lean:39,46` `pointwiseRelation`, `Proper` | `Pi.le_def`; `Relator.LiftFun`, `Mathlib/Logic/Relator.lean` | yes | **done** (this PR) — 0 uses, even inside the file |
| `HashSig/SLHDSA/WotsChecksum.lean:38` `Forall₂` (+ `length_eq` :43, `sum_le` :49, `take`, `drop`) | `List.Forall₂`, `Batteries/Data/List/Basic.lean:383`; `List.Forall₂.length_eq`, `Mathlib/Data/List/Forall2.lean:133`; `forall₂_take`/`forall₂_drop`, `:180,185`; `List.Forall₂.sum_le_sum`, `Mathlib/Algebra/Order/BigOperators/Group/List.lean:27` (`to_additive` of `prod_le_prod'`) | yes | **done** (this PR) — `sum_le_sum` needs `Mathlib.Algebra.Order.Ring.Nat` for `AddLeftMono ℕ`; `append_inv` is re-proved from `forall₂_take_append`/`forall₂_drop_append` (`:190,196`); `eq_of_sum_eq` :57 is new content and stays |
| `VCVio/OracleComp/SimSemantics/StateT/PreservesInv.lean:54` `QueryImpl.PreservesInv` | local `StateT.PreservesInv` :143 | — | **open (internal)** — the first unfolds to `∀ t, StateT.PreservesInv (impl t) Inv`; redefine it that way, `preservesInv_iff := Iff.rfl` |
| `Examples/ProgramLogic/RelationalDerived.lean:10` `public import Cslib.Foundations.Data.PFunctor.Free` | — | — | **keep** — corrected while landing this PR: no identifier from the module is used, but removing the import breaks the file (`PFunctor.FreeM.instPure` is otherwise reachable only through `public meta import`, so the non-`meta` import is what makes the `pure` instance usable in definitions). A name search cannot see module-visibility dependencies; the row was wrong |
| `LibSodium/SHA2.lean` | — | — | **done** (this PR) — 0-byte file |
| `VCVio/OracleComp/Constructions/WithoutReplacement.lean:44` `List.length_eq_countP_add_countP_not` | `List.length_eq_countP_add_countP`, `Init/Data/List/Count.lean:66` | yes | **done** (this PR) — `¬p a` vs `!p x`, bridged by `simp` |
| `ToMathlib/General.lean:246` `vector_eq_nil` (with a `warning.simp.varHead` suppression) | `List.Vector.eq_nil`, `Mathlib/Data/Vector/Defs.lean:209` | yes | **done** (this PR) — same statement |
| `ToMathlib/General.lean:580` `List.foldlM_range` | `Fin.foldlM_eq_foldlM_finRange`, `Init/Data/List/FinRange.lean:73` | yes | **done** (this PR) — symmetric statement |
| `ToMathlib/General.lean:408` `Finset.count_toList` | `List.Nodup.count`, `Init/Data/List/Pairwise.lean:348`, with `Finset.nodup_toList`/`mem_toList` | yes | **done** (this PR) |
| `ToMathlib/General.lean:37–109` `sum_update_succ_count`, `sum_update_pred`, `sum_filter_update_*` | `Finset.sum_update_of_mem`, `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:246` | yes | **done** (this PR) — re-prove as one-line corollaries; `QueryBound.lean:1196` already uses the upstream lemma |
| `HashSig/SLHDSA/WotsChecksum.lean:279` `sum_le_length_mul` | `List.sum_le_card_nsmul`, `Mathlib/Algebra/Order/BigOperators/Group/List.lean:92` | yes | **done** (this PR) — `smul_eq_mul` |
| `HashSig/SLHDSA/WotsChecksum.lean:188–239` `mod_pow_succ_extract` (52 lines) | `Nat.mod_pow_succ`, `Init/Data/Nat/Mod.lean:79` | yes | **done** (this PR) — identical up to `mul_comm`/`add_comm` |
| `VCVio/OracleComp/Constructions/SampleableType.lean:364–370` hand-built `List.Vector α n ≃ (Fin n → α)` | `Equiv.vectorEquivFin`, used at `Mathlib/Data/Fintype/Vector.lean:24–28` | yes | **done** (this PR) |
| `VCVio/OracleComp/QueryTracking/Structures.lean:321` `QueryCount.single i := Function.update 0 i 1` | `Pi.single i 1`, `Mathlib/Algebra/Notation/Pi/Basic.lean:30` (definitionally equal) | yes | **done** (this PR) — redefine; 50 consumers then use `Pi.single_eq_same/of_ne`, `Finset.sum_pi_single'` instead of hand case splits |
| `VCVio/EvalDist/Defs/Support.lean:31–41` `SetM.pure_def/bind_def/run_eq` | local `SetM.run_pure/run_bind/run_map`, `ToMathlib/Data/Set/Functor.lean:36–45` | — | **done** (this PR) — two simp normal forms for one term; keep the `run_*` family |
| `ToMathlib/Control/Monad/Indexed.lean` (whole file) | `PolyFun/Control/Monad/Indexed.lean` (verbatim copy; `ireturn`↔`ipure` only) | yes | **done** (this PR) — both declare a root-namespace `class IndexedMonad`; delete the copy, import PolyFun's from `Graded.lean` |
| `ToMathlib/Control/WriterT.lean:30` `LawfulAppend` | `Std.Associative (·++·)` + `Std.LawfulIdentity (·++·) ∅`, `Init/Core.lean:2478,2542`; `List` instances `Init/Data/List/Basic.lean:627,647` (re-proved locally at `:51`) | yes | **deferred** — 49 sites in 8 files, the reverse associativity orientation, `grind =` attributes, and Mathlib's `LawfulMonad (WriterT ω M)` only for `[Monoid ω]`: over 100 lines of churn, so recorded rather than done |
| `LatticeCrypto/Ring/Norms.lean:74` `centeredRepr` + six restated lemmas `:78–136` | `ZMod.valMinAbs`, `Mathlib/Data/ZMod/ValMinAbs.lean:23–29`; `natAbs_valMinAbs_le`, `natAbs_valMinAbs_neg`, `coe_valMinAbs`, `valMinAbs_mem_Ioc`, `valMinAbs_spec` | yes | **open** — the file already proves `centeredRepr_eq_valMinAbs` (`:139`) |
| `LatticeCrypto/Ring/Core.lean:204–210` `polyCoeffFinsetSum` | `Polynomial.finsetSum_coeff`, `Mathlib/Algebra/Polynomial/Coeff.lean` | yes | **open** — verbatim |
| `LatticeCrypto/MLDSA/Concrete/NTT.lean:82–129` `zeta_pow_256`, `MLKEM/Concrete/NTT.lean:106–156` `zeta_pow_128`, both `nInv_stageScalar` | `reduce_mod_char`, `Mathlib/Tactic/ReduceModChar.lean` | yes | **open** — one line each (verified); `square_mod` helper goes with them |
| `LatticeCrypto/MLKEM/Concrete/Encoding.lean:510–520` `decode12Pair_fst/snd` | `omega` | — | **open** (verified) |
| `Extern/MLDSA/NonVacuity.lean:36–38,98`, `Extern/MLDSA/Laws.lean:236` docstrings citing a `native_decide` NTT certificate | — | — | **open (docs)** — the certificate was retired by #614; no `native_decide` remains in the proof libraries |
| `ToMathlib/Data/ENNReal/AbsDiff.lean:51–55` private `tsub_le_tsub_add_tsub` | `tsub_le_tsub_add_tsub`, `Mathlib/Algebra/Order/Sub/Defs.lean:138` (same name, same statement) | yes | **done** (this PR) |
| `VCVio/EvalDist/Inequalities.lean:41–44` private `tsum_sub_tsum_le_tsum_sub` (unused hypothesis) | local `ENNReal.tsum_tsub_le_tsum_tsub`, `ToMathlib/Data/ENNReal/AbsDiff.lean:114` | — | **done** (this PR) |
| `VCVio/CryptoFoundations/Asymptotics/Negligible.lean:43–46` `negligible_of_le` | `SuperpolynomialDecay.trans_eventuallyLE`, `Mathlib/Analysis/Asymptotics/SuperpolynomialDecay.lean:133–138`, with `g := 0` | yes (`IsOrderedRing ℝ≥0∞`, `Mathlib/Data/ENNReal/Basic.lean:143`) | **open** — restate through it; gains eventually-≤ |
| `ToMathlib/Data/ENNReal/SumSquares.lean:63–80` `sq_sum_div_card_le_sum_sq` (17 lines) | `ENNReal.div_le_of_le_mul`, `Mathlib/Data/ENNReal/Inv.lean:386` | yes | **open** — keep the statement, two-line proof |
| `Examples/PRFTagReader/Asymptotic.lean:66–84` `negligible_natMul_of_poly_bound`, `negligible_ofReal_natDiv_of_poly_bound` | generic; belong in `Negligible.lean` | — | **open (internal)** — move |
| `ToMathlib/ProbabilityTheory/OptimalCoupling.lean:110` private `spmf_ext`; `LatticeCrypto/Ring/Kernel.lean:149` `poly_ext` | local `@[ext] SPMF.ext` (`SPMF.lean:187`), `@[ext] PolyBackend.ext_coeff` (`Ring/Core.lean:142`) | — | **done** (this PR) — wrappers over the `@[ext]` lemmas they call |

### Keep — genuinely VCVio's, or the upstream form does not fit

| VCVio | Why |
|---|---|
| `ToMathlib/General.lean:441` `card_bitVec` | Upstream `FinEnum.card_bitVec` (`FinEnum.lean:311`) is about `FinEnum.card`, not `Fintype.card`. Restate as `Fintype.card_bitVec := FinEnum.card_eq_fintypeCard.symm` once the instance above is gone. |
| `ToMathlib/General.lean` `BitVec.xor_self_xor` | Core has `xor_assoc`, `xor_self`, `zero_xor` (`Init/Data/BitVec/Lemmas.lean:1602,1614,1625`) but no `x ^^^ (x ^^^ y) = y` simp lemma; the local `@[simp]` is load-bearing by simp at `VCVio/EvalDist/BitVec.lean`. Upstream-to-core candidate. |
| `ToMathlib/General.lean:400` `Finset.sum_boole'` | `Finset.sum_boole` (`Mathlib/Algebra/BigOperators/Ring/Finset.lean:44`) is the `r = 1` case only; searched `sum_boole_nsmul`, `sum_ite_const`, `sum_boole_mul` — none is the `#filter • r` form. Re-prove via `sum_ite`, `sum_const_zero`, `sum_const`. |
| `ToMathlib/Control/WriterT.lean:107–135` `run_monadLift'`, `liftM_def'`, `run_pure'`, `run_bind'`, `run_map'` | Mathlib's `WriterT.run_pure/run_map/run_bind/run_liftM` (`Mathlib/Control/Monad/Writer.lean:93–121`) are generic in `empty append` under `letI := monad empty append`; the primed forms are their instance-specialised simp shapes (`Prod.map f id` vs `fun (a, w) ↦ (f a, w)`), with 25 call sites in `CryptoFoundations/FiatShamir/Sigma/Fork.lean` and `MacFromPRF.lean` that chain `support_bind`/`Set.image_singleton` after them. Keep the statements; prove them by the upstream lemmas. The "7 sorries" once attributed to this file are comment text (`scripts/axiom_baseline.json` has no WriterT entry). |
| `ToMathlib/Data/Set/Functor.lean:36–45` `SetM.run_pure/run_bind/run_map` | Upstream `Mathlib/Data/Set/Functor.lean` ends at `SetM.run` (line 190 of 190) with no `run_*` equations; the local lemmas are wrapper-boundary statements whose proofs already are `Set.pure_def`/`bind_def`/`fmap_eq_image`. Consumers in `VCVio/OracleComp/EvalDist.lean`. Upstream candidate. |
| `ToMathlib/Data/ENNReal/AbsDiff.lean:40` `ENNReal.absDiff` | `absDiff a b = edist a b` is provable (15 lines, compiled during the survey), but `ℝ≥0∞` is only a `WeakEMetricSpace` at the pin (`Mathlib/Topology/EMetricSpace/Weak.lean:247`; `PseudoEMetricSpace ℝ≥0∞` does not synthesize), so none of the local API is derivable from `edist`. Add `absDiff_eq_edist` as the bridge. |
| `ToMathlib/Data/ENNReal/SumSquares.lean` `sq_sum_le_card_mul_sum_sq` | Name-collides with `Mathlib/Algebra/Order/Chebyshev.lean:136`, whose hypotheses are ordered-ring; `ℝ≥0∞` is not. Keep under the `ENNReal` namespace with a docstring cross-reference. |
| `List.Vector` in 30 files (`MerkleTree/{Inductive,Addressed,MultiExtractability}/**`, `EvalDist/List.lean`, `Examples/PRGfromPRF.lean`, `ToMathlib/General.lean`) | Mathlib's `Mathlib/Data/Vector/Defs.lean` docstring steers verification code to core `Vector`, but core `Vector` has no `cons`, `head` needs `[NeZero n]`, `tail : Vector α (n-1)` (`Init/Data/Vector/Basic.lean:138,416`), and no `inductionOn`; no `List.Vector ↔ Vector` conversion exists in core, Batteries, or Mathlib (grep `toListVector\|List.Vector.toVector\|ofListVector` empty). The Merkle proofs are cons/nil inductions along depth. Keep. The one migration that is free: a core-`Vector` `SampleableType` instance beside the `List.Vector` one in `VCVio/OracleComp/Constructions/SampleableType.lean`. |
| `@[reducible]` on `OracleComp`, `OracleSpec.toPFunctor`, `ofFn`, `unifSpec`, `ProbComp`, `QueryImpl` | Type-level constructors; instance discrimination-tree keys depend on them (`docs/agents/gotchas.md` §7). |
| `scripts/AxiomSweep.lean` | `leanprover-community/axiom-audit` (reachable through `lean-action`'s `axiom-audit` input) is allowlist-only with **no committed baseline**, so it cannot express the shrink-only `sorryAx` ratchet (40 entries on `main`) or the `._native.` zero-debt rule (now with an empty grandfathered list: no `native_decide` remains in the proof libraries). |
| Sub-probability, TV/Rényi/KL divergences, couplings, `NegativeHypergeometric`, `MeasurableSpace (Option/Except)`, the `ToMathlib/Control` monad-theory files, `OrderEnrichedCategory`, `FinRatPMF`, the `LatticeCrypto/Ring` backend, the concrete SHA-2/Keccak/FPR implementations | Verified absent from the pinned trees by keyword grep (`IsSubprobability`, `Coupling` (only Gromov–Hausdorff hits), `hypergeometric`, `MeasurableSpace (Option`, `DijkstraMonad\|GradedMonad\|IndexedMonad\|RelativeMonad\|OrderedMonad\|MonadTransformer`, `MonoidalCategory Preord`, `NTT\|negacyclic`). |

### Upstream — belongs elsewhere (recorded; not opened in this sweep)

| VCVio | Target | Evidence of absence |
|---|---|---|
| `CommApplicative` instances for `Id`, `Option`, `Except ε` (`[Subsingleton ε]`), `ReaderT` (from `Commutative.lean`) | `Mathlib/Control/Basic.lean` | `grep -rn "instance.*CommApplicative" Mathlib` → 5 hits, none of these |
| `ToMathlib/Data/FinEnum.lean:61` `FinEnum Bool`, `Sym.finEnum`, `Equiv.Perm.finEnum`, `Function.Embedding.finEnum` | `Mathlib/Data/FinEnum.lean` | Mathlib has `Fintype (Sym α n)` (`Data/Fintype/Vector.lean:47`) and `Fintype (α ↪ β)` but no `FinEnum` versions |
| `VCVio/OracleComp/Constructions/SampleableType.lean:300–308` `FinEnum (ZMod n)`, `FinEnum USize`, `FinEnum ISize`; `arrayVectorEquivFin`, `instFintypeVector` | `Mathlib/Data/FinEnum.lean`; `Mathlib/Data/Fintype/Vector.lean` (which covers `List.Vector` only, `:27`) | grep of core/Batteries/Mathlib for `Vector α n ≃ (Fin n → α)` forms empty |
| `ToMathlib/General.lean` core-`Vector` `cases`/`induction`/`cases₂`/`induction₂` | core `Init/Data/Vector/` | core has only `elimAsArray`/`elimAsList` (`Init/Data/Vector/Basic.lean:71,78`) |
| `ToMathlib/Control/WriterT.lean:30` `LawfulAppend` | core (or just use `Monoid`) | no `LawfulAppend` in core/Batteries/Mathlib |
| `ToMathlib/Control/Lawful/MonadFunctor.lean:20,31`, `MonadControl.lean:23,39` `LawfulMonadFunctor(T)`, `LawfulMonadControl(T)` | core `Init/Control/Lawful/` next to `LawfulMonadLift(T)` (`Init/Control/Lawful/MonadLift/Basic.lean:29,44`, the exact template) | class-keyword grep across five trees |
| `HashSig/SLHDSA/WotsChecksum.lean` `Forall₂.eq_of_sum_eq` | `Mathlib/Data/List/Forall2.lean` | no statement of this shape upstream |
| `ToMathlib/Data/Set/Functor.lean` `SetM.run_*`; `BitVec.xor_self_xor` | Mathlib / core | see Keep |

### Track — heading into core, or blocked on a design decision

**Program logic: core is absorbing Loom's design.** Core ships two complete WP stacks at the
pin: the public `Std/Do/` (`SPred`/`PostShape`-indexed; conjunctivity is a *field* of
`PredTrans`, `Std/Do/PredTrans.lean:63–70`) and `Std/Internal/Do/` (lattice-generic over
`Lean.Order.CompleteLattice`, `Std/Internal/Do/Order/Basic.lean:15–20`). On `master` the
latter becomes public `Std.WP` with `LawfulWPMonadAttach`, and `mvcgen` is deprecated for
`vcgen`; none of it is in `v4.34.0-rc2`, so all of it is **v4.35**. VCVio's
`VCVio/ProgramLogic/{Unary,Relational}/Loom/*` and `ToMathlib/Control/Monad/RelWP.lean` sit on
loom2's `Std.Do'` three-parameter `WP m Pred EPred` — the design being upstreamed. Loom may be
imported only by those five files (`VCVio/ProgramLogic/Tactics/Unary/Internals.lean`,
`Unary/Loom/{Qualitative,Probabilistic,Quantitative}.lean`, `ToMathlib/Control/Monad/RelWP.lean`).
The obstacle is total: pinned Mathlib has **zero** `Lean.Order` occurrences, VCVio's `ℝ≥0∞`/`Prob`
lattice instances come from loom2 (`Loom/LatticeExt.lean:18–22`), and `NotationCore.lean` bakes
`Lean.Order.bot` into notation; 19 files touch `Lean.Order`. First step at 4.35: a
`ToMathlib/Order/LeanOrderBridge.lean` giving `Lean.Order.CompleteLattice` from Mathlib's for
`ℝ≥0∞`, then drop `Loom.WP.Basic`.

**Do not retarget `mvcgen` before 4.35.** Real invocations live in
`VCVio/ProgramLogic/Unary/{HandlerSpecs,StdDoExamples}.lean` and call core `Std.Do`
(`Std/Tactic/Do/Syntax.lean:436`), which is *not* deprecated at the pin; every other
occurrence is docstring prose. VCVio's own `syntax (name := vcgenBasic) "vcgen" : tactic`
(`VCVio/ProgramLogic/Tactics/Unary.lean:321`) shares its token with core `vcgen` (`:464`);
both parse into a `choice` node, and `evalChoiceAux` only falls through on `unsupportedSyntax`.
No file imports both today. Decide the rename with the retarget.

**`docs/agents/program-logic.md:679`** described the 4.29 state ("Lean v4.29.0 ships
`mvcgen`…"); the Sym-based `vcgen` is in core at 4.33 under `Lean.Elab.Tactic.Do.Internal`.
Refreshed in #653, which also adds the name-collision canary `VCVioTest/VCGenAmbiguity.lean`
and records the Loom import allowlist in `docs/agents/module-system.md`.

**Transparency.** `attribute [implicit_reducible] OracleSpec` (`VCVio/OracleComp/OracleSpec.lean:44`)
is documented as making the wrapper unfold during instance synthesis, but at the pin
`[implicit_reducible]` unfolds at `.implicit` only (`Lean/ReducibilityAttrs.lean:214–216`),
instance synthesis runs at `.instances` (`Lean/Meta/SynthInstance.lean:963`), and `.instances`
"does *not* unfold `[implicit_reducible]`" (`Init/MetaTypes.lean:123–125`). The `HAdd`
instance case was already fixed by #542 (left at the `instance_reducible` the `instance`
command supplies). **Resolved by experiment (#650):** removing the attribute leaves instance
synthesis at the erased `PFunctor.mk` literal intact (the canary in
`VCVioTest/PFunctorFacade.lean` passes without it) but breaks the `.implicit`-transparency
checks of dependent types (`QueryTracking/RandomOracle/EagerTable.lean`) and of
instance-implicit arguments (`Decidable` searches in
`MerkleTree/Inductive/Batch/Disagreement.lean` time out), so it stays with a comment that says
so. Of the twelve `attribute [local implicit_reducible]` sites, six are load-bearing
(`Coupling`, `Structures`, `EvalDist/PFunctor`, `Traversal`, `Coercions/Add`, `ReplayFork`) and
six compiled without and were deleted. Demoting `evalDist` from `@[reducible]` is deferred to
after the #637 rework: its first failure is the `LawfulEvalDistSemantics (FreeM P)` instance,
whose fields only unify through the reducible wrapper. `warn.redundantExpose` is on by default
(`Lean/Elab/MutualDef.lean:1190`); `linter.redundantVisibility` is off by default
(`Lean/Elab/DeclModifiers.lean:17`) and is switched on by the Track A lakefile PR.

**`QueryCount ι := ι → ℕ`** (`VCVio/OracleComp/QueryTracking/Structures.lean:299`, `@[reducible]`,
with `instance : Monoid (QueryCount ι)` at `:304` using `mul := +`): because the definition is
reducible, `#synth Monoid (ℕ → ℕ)` in the VCVio closure returns `QueryCount.instMonoid` — a
multiplicative monoid leaks onto every `ι → ℕ`. The repo already uses `κ →₀ ℕ` in
`QueryTracking/ResourceProfile.lean`. 161 references across 16 files; design issue, not a
sweep PR.

**NTT multiplication laws are assumed, not proved.** `multiplyNTTs` is defined as
`ntt (negacyclicMul (invNTT f) (invNTT g))` (`LatticeCrypto/MLDSA/Concrete/NTT.lean:262–264`, likewise
ML-KEM), so `toHat_mul` is tautological and the executable `loopMultiplyNTTs` is trusted through
`implemented_by`; Falcon's `Primitives.Laws.transform : NTTRingLaws` (`LatticeCrypto/Falcon/Primitives.lean:297`)
is a structure field. Mathlib supplies the twiddle half (`IsPrimitiveRoot` + `reduce_mod_char`) and the
CRT half (`Ideal.quotientInfRingEquivPiQuotient` and friends); the Cooley–Tukey bit-reversal lemma is
not in Mathlib or core and is the several-hundred-line remainder. See the lattice reading below.

**Matrix conventions.** SIS states `A *ᵥ x` (column), `NoisyLearning` states `s ᵥ* A` (row), ML-DSA
uses nested-`Vector` `matVecMul`; pick one and route through `PolyMatrix.toMatrix`.

**Cost-instrumentation layers.** `CostModel`, `CountingOracle`, `WriterCost`, `QueryCost` are
four presentations; `AddWriterT` (`WriterCost.lean`) is canonical and
`CostModel.expectedCost` already delegates to `AddWriterT.expectedCost`. The odd one out is
`CountingOracle.withCost` on the multiplicative `QueryCount` writer, blocked by the item above.

**`OracleSpec` operations vs PolyFun** (PolyFun `corrections.md` item 4): `OracleSpec`'s
`+`/`×`/`Σ`/`Π` are re-declared for `ι → Type` indexing but are `rfl`-bridged to
`PFunctor.sum/sigma/pi` (`toPFunctor_add/sigma/mul/pi` in `OracleSpec.lean`); the theory is
not re-proved. `QueryImpl`/`ProbHandler` vs PolyFun `Sampler`/`Decoration` (item 3) remains
two vocabularies for one concept; reconcile when the Kleisli–Mealy wiring lands.

**Deprecated aliases.** 25 `@[deprecated (since := "2026-06-25")] alias` blocks and 5 dated
2026-08-20 remained; no old name had a use in the repo; `docs/agents/gotchas.md` §18 already
forbids deprecated aliases. Deleted in #647 (38 of 39; the 39th,
`evalDist_eq_evalSPMF_toMeasure`, is undeprecated by #637 as the adapter's defining equation).

**Fully commented-out modules.** `Examples/Regev.lean` (2 live lines of 553) and
`Examples/FrankingProtocol.lean` (2 of 296) were imported by `Examples.lean`; `gotchas.md` §5
says delete. Deleted in #647, with the commented blocks in `Dijkstra`/`MonadControl`/`WriterT`
and 20 no-op `BigOperators` opens.

## Mathlib reading: idioms and integration candidates

A broad reading of the Mathlib (and core, Batteries, cslib) areas adjacent to VCVio, comparing
spellings idiom by idiom. Each area lists the objects VCVio's concepts correspond to, the
places where VCVio's spelling fights Mathlib's, and concrete integration candidates ranked by
leverage. Evidence is `file:line` in the pinned trees; `M:` is Mathlib, `C:` core/Std, `B:`
Batteries, `Cs:` cslib, `V:` VCVio `main`. Design constraints already accepted
([`denotational-probability-semantics.md`](denotational-probability-semantics.md): Measure-primary,
`Pr[…]` kept as the discrete façade, no global `Monad Measure`) are respected throughout.

### Probability and measure theory

**Correspondence.** `𝒟[mx]` is a `Measure`; the local `IsSubprobabilityMeasure`
(`V:ToMathlib/MeasureTheory/Measure/Subprobability.lean:37`) has no upstream twin
(`grep -rni 'subprobability\|SubMarkov'` → 0; `IsZeroOrProbabilityMeasure` is incomparable).
`evalSPMF` is `OptionT PMF`; `probOutput` is `μ {x}`; `probEvent` is `μ {x | p x}` and
`PMF.toOuterMeasure` (`M:Probability/ProbabilityMassFunction/Basic.lean:137`) is already the
`OuterMeasure.sum` of weighted diracs, so the integration doc's proposed form is `rfl`;
`expectedValue` is `∫⁻` (`M:MeasureTheory/Integral/Lebesgue/Basic.lean:56`); `Fintype.mPi` is
`Measure.pi` (`M:MeasureTheory/Constructions/Pi.lean:210`); `evalDistKernel` is
`Kernel.ofFunOfCountable` (`M:Probability/Kernel/Basic.lean:237`); a per-query family
`(t : Domain) → Measure (Range t)` is a *dependent* kernel, which Mathlib's non-dependent
`Kernel α β` (`M:Probability/Kernel/Defs.lean:55`) does not express. Mathlib has no
event-probability notation at all (`M:Probability/Notation.lean` defines `𝔼[·]`, `P[·]`, `∂P/∂Q`,
`ℙ`, `=ₐₛ`), so keeping `Pr[…]` is not a deviation. `PMF.bernoulli`/`binomial` are deprecated in
favour of the measures `Ber(x,y,p)` / `Bin(n,p)` (`M:Probability/Distributions/{Bernoulli,Binomial}.lean:50,62`).

**Idioms VCVio fights.**
- *Factor order at every bridge.* `lintegral_countable'` (`M:…/Lebesgue/Countable.lean:121`)
  yields `∑' a, f a * μ {a}` (mass right); VCVio's normal form is `Pr[= x | mx] * g x` (mass left),
  so every bridge proof ends in `tsum_congr fun _ => mul_comm` (`V:VCVio/EvalDist/Defs/Measure.lean:215`,
  `V:VCVio/EvalDist/ExpectationMeasure.lean:66`, `V:ToMathlib/Probability/ProbabilityMassFunction/Measure.lean:63`).
  One local `lintegral_countable'_comm` closes them by `simp`.
- *`ite` vs `Set.indicator`.* Mathlib's dirac normal form is `dirac_apply' : dirac a s = s.indicator 1 a`
  (`M:MeasureTheory/Measure/Dirac.lean:44`); VCVio's is `if x = y then 1 else 0`.
  `probEvent_eq_tsum_indicator`/`_ite` (`V:VCVio/EvalDist/Defs/Basic.lean:250,262`) already carry both.
- *Side conditions.* `Measure.map_apply`/`bind_apply` need `Measurable`/`MeasurableSet`; on discrete
  types these are `Measurable.of_discrete`/`MeasurableSet.of_discrete`, which VCVio invokes by hand
  33× while `fun_prop` (which `Measurable.of_discrete` is tagged for, `M:…/MeasurableSpace/Defs.lean:561`)
  is used 2×. A discrete "measure bridge" simp bundle (`Measure.map_apply`, `Measure.bind_apply`,
  `Measurable.of_discrete`, `MeasurableSet.of_discrete`, `lintegral_countable'_comm`) is the measure-side
  analogue of `UnfoldEvalDist`.
- *Orientation.* Mathlib unfolds `Kernel.comp_apply`/`Measure.bind_apply` toward `lintegral`; VCVio's
  `Pr` set unfolds toward `tsum`; `ENNReal.tsum_mul_left/right` is used in both directions (65×/91×).
- *`ae` vs support quantifiers.* `∀ x ∈ support mx, p x` is `∀ᵐ x ∂𝒟[mx], p x`; the measure
  statements (`ae_iff_prob_eq_one` `M:…/Typeclasses/Probability.lean:172`, `Measure.ae_ae_of_ae_bind`
  `M:…/GiryMonad.lean:244`, `Kernel.ae_comp_iff`) are single filter atoms, which sidesteps the
  `grind` saturation cycle `docs/agents/probability.md` documents. `∀ᵐ` has 2 uses in `V:VCVio/`.

**Integration candidates (ranked).**
1. `evalDist_mPi : 𝒟[Fintype.mPi f] = Measure.pi fun i => 𝒟[f i]` (induction as in
   `V:VCVio/EvalDist/PFunctorMeasure/Core.lean:170`, transport by `Measure.pi_map_piCongrLeft`
   `M:…/Pi.lean:746`), after which `probOutput_mOfFn`/`probOutput_mPi`
   (`V:VCVio/EvalDist/IndepProduct.lean:69,287`) are `Measure.pi_singleton` (`:298`),
   `probEvent_coord_mPi` (`:314`) is `Measure.pi_pi` (`:290`), and "independent"/"same
   distribution" can be phrased with `IndepFun` (`M:Probability/Independence/Basic.lean:144`;
   `indepFun_iff_map_prod_eq_prod_map_map` `:703` is `probOutput_seq_map_prod_mk_eq_mul`
   `V:VCVio/EvalDist/Prod.lean:91` in measure form), `HasLaw` (`M:Probability/HasLaw.lean:39`) and
   `IdentDistrib` (`M:Probability/IdentDistrib.lean:71`) — all three have 0 uses in VCVio.
2. Measure-side twins of the expectation algebra: `expectedValue_bind/map/mono/add/const`
   (`V:VCVio/EvalDist/Expectation.lean:49–85`) via `lintegral_bind` (`M:…/GiryMonad.lean:285`),
   `lintegral_map` (`M:…/Lebesgue/Map.lean:27`), `lintegral_mono` (`M:…/Lebesgue/Basic.lean:84`),
   `lintegral_add_left` (`M:…/Lebesgue/Add.lean:314`), `lintegral_const` (`:110`); and the Markov
   bound `probEvent_le_tsum_probOutput_mul_cost` (`V:VCVio/EvalDist/Defs/Basic.lean:898`), which is
   `meas_le_lintegral₀` (`M:…/Lebesgue/Markov.lean:61`) on the nose. Duplicate, do not replace: the
   `tsum` forms are generic over `[MonadLiftT m SPMF]`.
3. Event algebra on the `𝒟` side: `probEvent_or_le` ↔ `measure_union_le`
   (`M:MeasureTheory/OuterMeasure/Basic.lean:88`), `probEvent_exists_finset_le_sum` ↔
   `measure_biUnion_finset_le` (`:80`), `probEvent_compl` ↔ `measure_add_measure_compl`
   (`M:…/MeasureSpace.lean:157`), `probEvent_mono` ↔ `measure_mono`.
4. `evalDist_bind_const`/`evalDist_map_const` from `Measure.bind_const` (`M:…/GiryMonad.lean:258`)
   and `Measure.map_const` (`M:…/Dirac.lean:91`): one-liners, absent today
   (`probOutput_bind_const` `V:VCVio/EvalDist/Monad/Basic.lean:432` is their `Pr` shadow).
5. Conditional probability is `ProbabilityTheory.cond` (`M:Probability/ConditionalProbability.lean:76`,
   `cond_apply` `:216`, Bayes `cond_mul_eq_inter` `:264`, total probability `cond_add_cond_compl_eq`
   `:268`): the hand-rolled divide-by-`Pr` family (`probEvent_bind_le_probEvent_div`
   `V:VCVio/EvalDist/Monad/Basic.lean:302`, `probOutput_bind_mono_div_const` `:658`,
   `probEvent_bind_congr_div_const` `:692`) and the Σ-protocol comment
   (`V:VCVio/CryptoFoundations/SigmaProtocol.lean:220–227`, "avoids conditional probability").
6. `MeasurableEmbedding (@some α)` for the coproduct σ-algebra
   (`V:ToMathlib/MeasureTheory/MeasurableSpace/Option.lean:28`; 0 uses of `MeasurableEmbedding` in
   VCVio): makes `Measure.dropNone μ = μ.comap some` on the nose (the ambiguity the design doc
   records) and unlocks `MeasurableEmbedding.lintegral_map`, `Measure.map_injective`,
   `Kernel.comapRight`, `isProbabilityMeasure_comap`.
7. Hypothesis hygiene: bind laws (`V:VCVio/EvalDist/Defs/Measure.lean:85`,
   `V:VCVio/EvalDist/PFunctorMeasure/Core.lean:133`) ask `Measurable`, Mathlib's
   `bind_apply`/`bind_bind`/`lintegral_bind` ask `AEMeasurable`; `Measure.toSPMF`
   (`V:…/Defs/Measure.lean:236`) takes `hμ : μ univ ≤ 1` where the class exists and Mathlib's
   `Measure.toPMF` takes `[IsProbabilityMeasure μ]`; `SPMF.toMeasure_bind` (`:205`) needs countability
   on both sides only because it goes through `ext_of_singleton`.
8. Bind-swap `evalSPMF_bind_bind_swap` (`V:VCVio/EvalDist/Monad/Basic.lean:885`) is `PMF.bind_comm`
   (`M:…/Monad.lean:144`) through `SPMF.toPMF_bind`, or Tonelli `lintegral_lintegral_swap`.
9. Discrete density normal form `𝒟[mx] = Measure.count.withDensity (Pr[= · | mx])` (generalising
   `V:ToMathlib/Probability/ProbabilityMassFunction/RadonNikodym.lean:49`), the form in which
   `Measure.rnDeriv`, `klDiv_eq_lintegral_klFun` (`M:InformationTheory/KullbackLeibler/Basic.lean:119`)
   and the local Rényi MGF compute. `Measure.sum_smul_dirac` (`M:…/Dirac.lean:138`) and
   `Measure.ext_of_singleton` (`:111`) are the companion normal form; `Measure.sum` has 0 uses.
10. Kernel API for the observation layer when it migrates: `∘ₖ`, `⊗ₖ`, `∥ₖ`, `⊗ₘ`,
    `Kernel.const/deterministic/compProd` all have 0 uses; `κ ^ n` with Chapman–Kolmogorov
    (`M:Probability/Kernel/Composition/Comp.lean:250–260`), `Kernel.Invariant`,
    `IsDeterministic`, `boolKernel`, `Kernel.ext_fun` (`M:…/Kernel/Defs.lean:255`, the kernel form of
    `evalSPMF_ext`). Moments (`mgf`, `cgf`, `evariance`, Chernoff, `Measure.tilted`,
    `M:Probability/Moments/*`) have 0 uses; `renyiMGF` is a Hellinger integral, `tilted` its companion.
11. Cauchy–Schwarz in `V:VCVio/EvalDist/Inequalities.lean:70` rests on the local
    `ENNReal.sq_tsum_le_tsum_sq`; Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq`
    (`M:MeasureTheory/Integral/MeanInequalities.lean:24`) at `p = q = 2` against `𝒟[mx]` is the
    upstream form and drops the `∑' w ≤ 1` hypothesis.

**Gaps confirmed** (search that came back empty in `M:`): subprobability measures and kernels;
`tvDist`/`totalVariation` for measures and PMFs (only `SignedMeasure.totalVariation`);
`absDiff`; Rényi/Hellinger divergences (only Erdős–Rényi, Hellinger–Toeplitz); couplings (only
Gromov–Hausdorff); `Measure.bind_mono_right`; measure-level `iSup_apply_of_monotone` (only
`OuterMeasure.iSup_apply`); `PMF.toMeasure_bind` at measure level (only `toMeasure_bind_apply`);
`MeasurableSpace (Option _)`/`(Except _ _)`; `BitVec` measurability; negative hypergeometric;
`uniformOn_prod` (only `uniformOn_pi`). Discrete-instance policy matches Mathlib's
(`M:MeasureTheory/MeasurableSpace/Instances.lean:22–40`): `⊤` per type, no blanket `[Finite α]` instance.

### Control, monads, order

**Correspondence.** `OracleComp spec = PFunctor.FreeM spec.toPFunctor` is cslib's polynomial free
monad re-exported by PolyFun (`Cs:Foundations/Data/PFunctor/Free.lean:77`, whose docstring says it was
ported from VCVio); `simulateQ = FreeM.liftM` with PolyFun's `liftMHom_unique`
(`PolyFun/PFunctor/Free/Basic.lean:218`) as the universal property; `QueryImpl` is `PFunctor.Handler`
(`rfl`). `LawfulMonadLift(T)` (`C:Init/Control/Lawful/MonadLift/Basic.lean:29,44`) is consumed 432×;
Batteries' `LawfulAlternativeLift` and `LawfulMonadStateOf` (`B:Control/LawfulMonadState.lean:48`)
exist, the latter with 0 VCVio uses although `V:VCVio/OracleComp/SimSemantics/StateT/Basic.lean:15`
still says "once laws for it exist". `support` (a monad morphism into `SetM`) corresponds to core's
`MonadAttach.CanReturn` (`C:Init/Control/MonadAttach.lean:30`, lawful instances for
`ReaderT/StateT/ExceptT/OptionT`) and to `Functor.Liftp`/`Functor.supp` (`M:Control/Functor.lean:238,251`);
no bridge exists in either direction. `OrderedMonad` (`V:ToMathlib/Control/Monad/Ordered.lean:52`,
Mathlib `Preorder`) is the twin of core's `MonoBind` (`C:Init/Internal/Order/Basic.lean:879`,
`Lean.Order`), likewise unbridged.

**Idioms.** VCVio follows core's simp orientation (`bind_pure_comp` simp, `map_eq_pure_bind` not;
230× vs 9×) and the `liftM`/`run_liftM` lemma pattern; `seq_eq_bind` (28 hits) is deprecated since
2025-10-26 for `seq_eq_bind_map` (`C:Init/Control/Lawful/Basic.lean:188`). Mathlib's `@[monad_norm]`
set is used 166×; `functor_norm` 0×; the local `handler_simp` set has effectively one use and can fold
into `game_rule`. The carrier-indexed `WP m Pred EPred` with `outParam`s forces the
`scoped instance (priority := 1100)` pattern (`V:VCVio/ProgramLogic/Unary/Loom/Qualitative.lean:49–56`);
core's `WP m (ps : outParam PostShape)` avoids it because the shape is determined by the monad stack —
a genuine design divergence. Three definitionally different qualitative WPs coexist
(`MAlgOrdered.wp` over Mathlib lattices, 252 uses; loom2's `Std.Do'.wp`, 427; core `Std.Do.wp` bridged
at `.pure` shape only, `V:VCVio/ProgramLogic/Unary/StdDoBridge.lean:70–76`); the missing lemma is
`Std.Do.wp x Q = ⌜MAlgOrdered.wp x Q.1⌝` (both are `∀ a ∈ support x, …`).

**Integration candidates (ranked).**
1. `V:ToMathlib/Control/Monad/Indexed.lean` is a verbatim copy of `PolyFun/Control/Monad/Indexed.lean`
   (`ireturn`↔`ipure` rename only); both declare a root-namespace `class IndexedMonad`. Delete the copy,
   import PolyFun's from `Graded.lean`.
2. `SetM.pure_def/bind_def/run_eq` (`V:VCVio/EvalDist/Defs/Support.lean:31–41`) duplicate
   `SetM.run_pure/run_bind/run_map` (`V:ToMathlib/Data/Set/Functor.lean:36–45`) with a competing simp
   normal form; keep the `run_*` family (core's `StateT.run_*` idiom).
3. One generic `[CompleteLattice α] → Lean.Order.{PartialOrder,CompleteLattice} α`
   (`ToMathlib/Order/LeanOrder.lean`, `rel := (· ≤ ·)`, `has_sup c := ⟨sSup {x | c x}, …⟩`, low
   priority so core's `Prop` instance stays first) replaces the four hand instances
   (`V:VCVio/ProgramLogic/Unary/Loom/Quantitative.lean:121,132`, `Probabilistic.lean:106,134`); `Prob`'s
   lattice comes free from `Set.Iic 1` (`M:Order/CompleteLatticeIntervals.lean:227`). This is also the
   first step of the v4.35 `Std.WP` migration.
4. `LawfulAppend` (`V:ToMathlib/Control/WriterT.lean:30`) is `Std.Associative (·++·)` +
   `Std.LawfulIdentity (·++·) ∅` (`C:Init/Core.lean:2478,2542`; `List` instances
   `C:Init/Data/List/Basic.lean:627,647`, re-proved locally at `WriterT.lean:51`). 49 uses.
5. `MonadAttach (OracleComp spec)` with `CanReturn x a := a ∈ support x` and `LawfulMonadAttach`
   (support is the strongest postcondition by `support_bind`/`support_pure`); bridge
   `Functor.Liftp p x ↔ ∀ a ∈ support x, p a` so `allOutputsSatisfy` (`V:…/Support.lean:102`) is
   `Functor.Liftp` on the nose. Unlocks `MonadAttach.pbind` for well-founded recursion through binds.
6. `simulateQ_traverse`, `support_traverse`, `evalSPMF_traverse` from `LawfulTraversable.naturality`
   (`M:Control/Traversable/Lemmas.lean:66–123`; `simulateQ'` is a monad hom, hence an
   `ApplicativeTransformation`) subsume `simulateQ_list_mapM/forM/forIn`
   (`V:VCVio/OracleComp/SimSemantics/SimulateQ.lean:261–296`) and `simulateQ_optionT_vector_mapM_pure`
   (`:118`) at once; `Fin.mOfFn` (`V:ToMathlib/General.lean:571`) is `traverse` on `flip Vector n`
   (`M:Data/Vector/Basic.lean:709`, `List.Vector.mOfFn` `:387`).
7. State the `StateT` handler combinators (`withBadFlag`, `withBadUpdate`, `piStateT`,
   `V:VCVio/OracleComp/SimSemantics/StateT/Basic.lean:125–160`, and the projection lemmas) over
   `[MonadStateOf σ m] [LawfulMonadStateOf σ m]` so they apply to `StateT σ (OptionT …)` stacks
   without re-proof.
8. `QueryImpl unifSpec (RandG g) := fun n => Random.randFin` (`M:Control/Random.lean:38,102`)
   gives deterministic replay via `IO.runRandWith seed` (`:170`) for KAT-style tests, a *lawful*
   (`StateT`) simulation target, and `Random`/`SampleableType` interop; Batteries' `MersenneTwister`
   plugs in as a `RandomGen`. One-way bridge (`Random` has no laws).
9. `Monad.Commutative ↔ CommApplicative` under `LawfulMonad`; `CommApplicative PMF` from
   `PMF.bind_comm` (the commented-out `sorry` block at `Commutative.lean:201–208` is exactly this).
10. Dead `ToMathlib/Control` files (0 reverse deps): `Lawful/{MonadFunctor,MonadControl,MonadReader,
    MonadState}` (two are stubs), `AlternativeMonad`, `Monad/{Dijkstra,Graded,Relative,Commutative}`.
    Prune, `deprecated_module`, or move the sorry-free ones to PolyFun, where the category-theory
    imports they pull already live.
11. Low priority: `ULiftable` (`M:Control/ULiftable.lean:53`) for the 17 `ULift Bool` scheduler
    signatures in `V:VCVio/Interaction/UC/*`; `Relator.LiftFun` (`M:Logic/Relator.lean:34`) for
    `LawfulMonadRelation`/`rwp_mono` (cosmetic).

**Gaps confirmed** (0 hits in Mathlib, core, Batteries): `MonadTransformer`, `LawfulMonadFunctor`,
`LawfulMonadControl`, `LawfulAppend`, `MonadRelation`, `OrderedMonad`, `DijkstraMonad`, `GradedMonad`,
`RelativeMonad`, a bind-preserving unbundled monad-hom class (`ApplicativeTransformation`
`M:Control/Traversable/Basic.lean:77` is the pure/seq twin), relational WP. `OrderHom.gfp`,
`OmegaCompletePartialOrder`, `Part`, `partial_fixpoint`, `MonoBind`, `MonadTail`, the `monotonicity`
tactic: present upstream, not hand-rolled against, 0 uses (the one place a fixed-point library would
help is a `CCPO` on `ITree`, PolyFun-side).

### Computability and cslib

**Correspondence.** VCVio/PolyFun machines are typed coalgebras with oracle ports
(`PolyFun/Realizability/Machine.lean:87,132`); Mathlib's `Turing.TM0/1/2` and cslib's
`SingleTapeTM`/`MultiTapeTM`/`URM` are closed word transducers with no query port. PolyFun's
`StepClass.computable` already sets `Str := Primcodable`, `Hom := Computable`
(`PolyFun/Realizability/Instances.lean:142–233`), so Mathlib's computability theory is a *qualitative*
backend today; nothing in VCVio exercises it (`IsRealizableBy StepClass.computable` has 0 examples).
Mathlib's only polytime notion, `TM2ComputableInPolyTime`, has `proof_wanted` composition
(`M:Computability/TuringMachine/Computable.lean:284`); cslib's `PolyTimeComputable.comp`
(`Cs:Computability/Machines/Turing/SingleTape/Deterministic.lean:490`) is proved — which is why the
in-flight cslib route (VCVio #576, PolyFun #178/#179) is the right one. `Encodable`/`Nat.pair` cannot
serve polynomial classes (`Nat.pair` is quadratic in value, `M:Data/Nat/Pairing.lean:136`; list encoding
exponential). cslib's `TimeM T` (`Cs:Algorithms/Lean/TimeM.lean:49`) is `AddWriterT T Id` with trusted,
unverified ticks (cross-reference only). PolyFun's `CodeRetract (List Γ) A` is Mathlib's
`Computability.Encoding A Γ` (`M:Computability/Encoding.lean:40`) up to field names (PolyFun-side).

**Integration candidates.**
1. A generic dependent pairing lemma `Pr[= (x, y) | do let a ← mx; let b ← f a; return (a, b)] =
   Pr[= x | mx] * Pr[= y | f x]` — cslib's `PMF.bind_pair_apply` (`Cs:Probability/PMF.lean:49`) — is
   absent from VCVio: `V:VCVio/EvalDist/Prod.lean:145` has only the independent case and
   `V:VCVio/CryptoFoundations/SymmEncAlg.lean:51` re-proves the dependent case inline for the
   encryption experiment.
2. `perfectSecrecyAtAllPriors_iff_ciphertextRowsEqualAt` (`V:VCVio/CryptoFoundations/SymmEncAlg.lean:88`)
   assumes `[Finite M]`; cslib's `perfectlySecret_iff_ciphertextIndist`
   (`Cs:Crypto/Protocols/PerfectSecrecy/Basic.lean:39`) needs none, by distinguishing with the
   two-point prior `uniformOfFinset {m₀, m₁}`. The trick transfers verbatim.
3. Shannon's key-space bound `Nat.card K ≥ Nat.card M` (`Cs:…/PerfectSecrecy/Basic.lean:46`) is absent
   from VCVio (the converse constructions `*_of_uniformKey_of_uniqueKey`, `SymmEncAlg.lean:140–210`,
   exist).
4. A `PMF`-valued posterior (`Cs:Probability/PMF.lean:99 posteriorDist`) would let Bayes-style
   secrecy/privacy be stated as equalities of distributions; VCVio deliberately cross-multiplies
   (`perfectSecrecyPosteriorEqPriorAt`, `SymmEncAlg.lean:114`). cslib labels its file temporary and
   Mathlib-bound; prefer importing over copying if adopted.
5. Secret sharing is absent from VCVio (`grep -rliE "secret.?shar|shamir"` → only Fiat–Shamir); cslib has
   a full threshold scheme with privacy and Shamir (`Cs:Crypto/Protocols/SecretSharing/{Scheme,Shamir}.lean:52,291`),
   whose Lagrange lemma (`Shamir/Polynomial.lean:134`) is pure polynomial algebra reusable verbatim.
6. cslib `LTS.Bounded/Terminating/Acyclic` (`Cs:Foundations/Semantics/LTS/Termination.lean:30–81`) is
   the ready-made shape for the UC ping-pong boundedness phase (design doc phase 8); PolyFun's
   `Control.LTS` does not import cslib's (PolyFun-side).

**Dependency note.** VCVio's core datatype is definitionally cslib's `PFunctor.FreeM` through
PolyFun's re-export (`PolyFun/PFunctor/Free/Basic.lean:11`); the single direct cslib import in VCVio is
dead (see Adopt). The manifest on `main` pins cslib `98e395a7` (v4.33.1), inherited through PolyFun.

### `ℝ≥0∞`, infinite sums, and asymptotics

**Correspondence.** `negligible f := SuperpolynomialDecay atTop Nat.cast f`
(`V:VCVio/CryptoFoundations/Asymptotics/Negligible.lean:31–35`, `negligible_iff := Iff.rfl`) *is*
Mathlib's notion. But Mathlib's `SuperpolynomialDecay` file is stratified by typeclass
(`M:Analysis/Asymptotics/SuperpolynomialDecay.lean`): at `β = ℝ≥0∞` only the `CommSemiring` stratum
(`congr/zero/add/param_pow_mul`) and the `IsOrderedRing`+`OrderTopology` stratum
(`trans_eventuallyLE`, `:133–138`) apply; `const_mul`/`polynomial_mul` need `ContinuousMul`, which
`ℝ≥0∞` lacks (only `ENNReal.tendsto_mul` with side conditions,
`M:Topology/Instances/ENNReal/Lemmas.lean:316`), and the big-O/little-o characterizations
(`:292,307`) need a normed field, while `ℝ≥0∞` has only `ENorm`. So there is no `=O[atTop]` statement
for `ℕ → ℝ≥0∞` in Mathlib, and VCVio's `negligible_const_mul (hc : c ≠ ⊤)` /
`negligible_polynomial_mul (p : ℕ[X])` / `negligible_sum` are legitimately `ℝ≥0∞`-specific. Mathlib has
no `Negligible` (grep). VCVio has 0 uses of `IsBigO`, `IsLittleO`, `∀ᶠ`, `∃ᶠ`.

**The missing bridge is cheap.** `negligible f ↔ SuperpolynomialDecay atTop Nat.cast (toReal ∘ f)`
for `∀ n, f n ≠ ⊤` (≈6 lines from `ENNReal.tendsto_toReal_zero_iff`,
`M:Topology/Instances/ENNReal/Lemmas.lean:549`, `toReal_mul/pow/natCast`) and its `ofReal` twin
(`ENNReal.toReal_ofReal`). With it the whole field stratum applies on the `toReal` side
(`superpolynomialDecay_iff_isBigO`, `…_isLittleO`, `…_zpow_tendsto_zero`, `param_zpow_mul`) with
`hk := tendsto_natCast_atTop_atTop`. Today every consumer re-crosses `ℝ → ℝ≥0∞` by hand
(`V:Examples/PRFTagReader/Asymptotic.lean:300–310` chains seven `ENNReal.ofReal_add_le`;
`V:VCVio/Interaction/UC/Computational.lean:386–390`; `V:VCVio/CryptoFoundations/SecExp.lean:141–149`),
and the generic `negligible_natMul_of_poly_bound` / `negligible_ofReal_natDiv_of_poly_bound` live in
`Examples/PRFTagReader/Asymptotic.lean:66–84` instead of `Negligible.lean`.

**Idioms VCVio does not use** (counts over `V:{VCVio,ToMathlib,Examples,…}`):
- `lift a to ℝ≥0 using ha` then `norm_cast`: 39 uses in Mathlib's own `ENNReal` core files, 0 in
  VCVio, which crosses to `ℝ` via `toReal`/`ofReal` (142/249 references) instead.
- `finiteness` (`M:Tactic/Finiteness.lean`, an aesop rule set with `positivity` fallback, even used as
  an autoparam in statements: `tendsto_toReal_zero_iff (hf : … := by finiteness)`): a handful of uses vs
  dozens of hand-written `≠ ⊤` hypotheses, 69 `one_ne_top`, 50 `ne_top_of_le_ne_top`, and `aesop` calls
  whose only job is a `≠ ⊤` side goal (`V:ToMathlib/Data/ENNReal/Gauss.lean:224,229`).
- `gcongr`: 110 uses against ≈400 hand-written monotonicity steps (`mul_le_mul'` 103 — 29 in
  `V:VCVio/EvalDist/Monad/Basic.lean` alone, all of the shape `gcongr with x; exact h x` —
  `add_le_add` 98, `tsum_le_tsum` 136, `Finset.sum_le_sum` 39). `bound` is not a lever
  (only `ofReal_le_ofReal` is `@[bound]` on `ℝ≥0∞`).
- Side-condition-free division (`ENNReal.div_le_of_le_mul`, `mul_le_of_le_div`,
  `M:Data/ENNReal/Inv.lean:386,408`), `ENNReal.mul_le_mul_iff_right` (`M:Data/ENNReal/Operations.lean:74`),
  `ENNReal.le_of_forall_pos_le_add` (`M:Data/ENNReal/Basic.lean:607`): 0 uses; VCVio multiplies both sides
  by `2⁻¹ * 2` with two `inv_mul_cancel`s instead (`V:ToMathlib/Data/ENNReal/SumSquares.lean:36–44,124–131`).
- Stay in `ℝ≥0∞` and transfer once: `ℝ`-valued `tsum` proofs carry five to seven `Summable`/nonneg
  `have`s (`V:VCVio/EvalDist/TVDist.lean:240–270`, `V:VCVio/ProgramLogic/Relational/SimulateQ.lean:1315–1348`)
  where the `etvDist` statement in `ℝ≥0∞` (`ENNReal.tsum_le_tsum` is unconditional) followed by one
  `toReal_mono` is roughly 60 % shorter.
- `tsum` orientation is consistent with Mathlib (660 `∑'`, 0 `tsum (fun`).

**Integration candidates (ranked).**
1. The two bridge lemmas above in `Negligible.lean`, plus moving the two `_of_poly_bound` lemmas there.
2. `negligible_of_le` (`Negligible.lean:43–46`) is `SuperpolynomialDecay.trans_eventuallyLE` with
   `g := 0` (typeclasses verified against `M:Data/ENNReal/Basic.lean:143`); adopting it upgrades VCVio to
   eventually-≤ for free.
3. Delete the private `tsub_le_tsub_add_tsub` (`V:ToMathlib/Data/ENNReal/AbsDiff.lean:51–55`, Mathlib's
   `M:Algebra/Order/Sub/Defs.lean:138` with the same name and statement) and the private
   `tsum_sub_tsum_le_tsum_sub` (`V:VCVio/EvalDist/Inequalities.lean:41–44`, unused hypothesis), which
   duplicates VCVio's own `ENNReal.tsum_tsub_le_tsum_tsub` (`AbsDiff.lean:114`).
4. One lemma `tsum_probOutput_mul_le_of_le : (∀ x, f x ≤ c) → ∑' x, Pr[= x | mx] * f x ≤ c` next to
   `tsum_probOutput_mul_mono` (`V:VCVio/EvalDist/Monad/Basic.lean:998`) retires ≈8 hand-rolled copies of
   the `tsum_le_tsum (mul_le_mul' …) / tsum_mul_right / tsum_probOutput_le_one` chain
   (`V:VCVio/OracleComp/QueryTracking/Birthday.lean:44–46`,
   `V:VCVio/CryptoFoundations/Fischlin/KnowledgeSoundness.lean:1381–1385`, `Monad/Basic.lean:258–264,343–345,507–513`).
5. `sq_sum_div_card_le_sum_sq` (17 lines, `SumSquares.lean:63–80`) is two lines by
   `ENNReal.div_le_of_le_mul`; `add_div_two_mul_nat` (18 lines, `Gauss.lean:283–300`) is four by
   `ENNReal.mul_div_mul_left` + `div_add_div_same`.
6. `ENNReal.absDiff = edist` (weak metric on `ℝ≥0∞`) derives the four metric axioms; the rest of the
   `absDiff` API stays local because Mathlib's own TODO (`M:Topology/EMetricSpace/Weak.lean:267`) says the
   `edist`-on-`ℝ≥0∞` API is empty.

**Gaps confirmed** (`M:` grep): `∑' a - ∑' b ≤ ∑' (a - b)` (only the ℕ-indexed equality `ENNReal.tsum_sub`);
`edist`/`absDiff` API on `ℝ≥0∞`; `two_mul_le_add_sq`, Cauchy–Schwarz and Chebyshev on `ℝ≥0∞` (Mathlib's
need `MulPosStrictMono`/`IsStrictOrderedRing`/`Semifield`); `ℝ≥0∞`-`tsum` Hölder without `Summable`
(`V:ToMathlib/Analysis/MeanInequalities.lean:41` is upstreamable as stated); `toReal_sub_le_abs_toReal_sub`;
the `Iic` sum–integral comparison; `ℝ≥0∞` negligible closure under `const_mul`/finite sums.

### Finite data and algebra idioms

**Representation map.** VCVio's split — `Fin n → α` for tuples (180 hits, `Fin.cons` 55),
`List.Vector` for mathematics (MerkleTree, PRG, `EvalDist/List.lean`; 253 hits), core `Vector` for
executable code (LatticeCrypto, HashSig; 231 hits) — matches Mathlib's own guidance
(`M:Data/Vector/Defs.lean:14–32`). Core `Vector` has no `cons` and no induction principle
(`C:Init/Data/Vector/*`: only `exists_push`, `vector₂_induction`); VCVio's own proofs use the
core-idiomatic `push` decomposition (`V:VCVio/EvalDist/List.lean:352`, `V:ToMathlib/Data/Vector.lean:318`)
while `V:ToMathlib/General.lean:462–502` hand-rolls an `insertIdx 0` induction — two competing styles;
standardise on `push`. `QueryCount ι := ι → ℕ` with `mul := +` is `Multiplicative (ι → ℕ)`, and keeping
the plain function is justified (computable, pointwise `+`/`≤`); `ResourceProfile.usage : κ →₀ ℕ` is
the Mathlib idiom at the price of `noncomputable`, and there is no `Finsupp.equivFunOnFinite` bridge
between the two. `BitVec` (312) is idiomatic; the Fischlin files use `Fin (2 ^ b)` (241 hits) for a
random-oracle range that `BitVec.toNat` would serve equally. `ZMod` for coefficients, `ByteArray`/
`Vector UInt8 n` at the FIPS wire layer, `[Countable α]` for discrete measure semantics: all match
Mathlib's idiom. Finset notation: `#s` and `#{x ∈ s | p x}` have 0 code uses against 728 `.card` and
79 `univ.filter`; Mathlib now states lemmas in the new notation (`Finset.sum_boole`,
`Fin.card_filter_val_lt` `M:Data/Fintype/Fin.lean:47`), so `rw` increasingly needs it to line up.
`Finite` (219) / `Fintype` (403) / `FinEnum` (243) follow Mathlib's "computable `Fintype`, otherwise
`Finite`" rule; `SampleableType` is correctly built on `FinEnum`.

**Base-w digits.** ML-KEM already uses `Nat.digitsAppend`/`Nat.ofDigits`
(`V:LatticeCrypto/MLKEM/Concrete/Encoding.lean:233–276`); HashSig re-derives the theory big-endian
by hand (~90 hits across `WotsChecksum`, `Encoding`, `EncodingLemmas`, `WotsEncoding`): `toInt` is
`Nat.ofDigits 256 (x.map UInt8.toNat).reverse`, `toByte x len` is `(Nat.digitsAppend 256 len x).reverse.map
UInt8.ofNat`, `fromBaseW` is `Nat.ofDigits w ds.reverse`, `digitsOfBaseW` is
`(Nat.digitsAppend w len (n % w^len)).reverse`. FIPS 205 justifies the big-endian *definitions*; four
`reverse` bridge lemmas would connect `digitsOfBaseW_lt`, `fromBaseW_digitsOfBaseW_*`, `toInt_toByte_mod`
to `lt_of_mem_digitsAppend`, `setInvOn_digitsAppend_ofDigits`, `ofDigits_lt_base_pow_length`
(`M:Data/Nat/Digits/Lemmas.lean:344,363`, `Defs.lean:380`).

**Lemma-level duplicates verified by reading both declarations** (all added to the Adopt table):
`List.length_eq_countP_add_countP_not` ↔ core `List.length_eq_countP_add_countP`
(`C:Init/Data/List/Count.lean:66`, `¬p a` vs `!p x`); `vector_eq_nil` ↔ `List.Vector.eq_nil`
(`M:Data/Vector/Defs.lean:209`); `List.foldlM_range` ↔ `Fin.foldlM_eq_foldlM_finRange`
(`C:Init/Data/List/FinRange.lean:73`, symmetric); `WotsChecksum.sum_le_length_mul` ↔
`List.sum_le_card_nsmul` (`M:Algebra/Order/BigOperators/Group/List.lean:92`);
`WotsChecksum.mod_pow_succ_extract` (52 lines) ↔ `Nat.mod_pow_succ` (`C:Init/Data/Nat/Mod.lean:79`)
plus commutativity; `sum_update_succ_count`/`sum_update_pred`/`sum_filter_update_*`
(`V:ToMathlib/General.lean:37–109`) ↔ `Finset.sum_update_of_mem`
(`M:Algebra/BigOperators/Group/Finset/Piecewise.lean:246`), which `V:VCVio/OracleComp/QueryTracking/QueryBound.lean:1196`
already uses; `Finset.count_toList` ↔ `List.Nodup.count` (`C:Init/Data/List/Pairwise.lean:348`) via
`Finset.nodup_toList`; the hand-built equivalence in `instSampleableTypeListVector`
(`V:VCVio/OracleComp/Constructions/SampleableType.lean:364–370`) ↔ `Equiv.vectorEquivFin`
(`M:Data/Fintype/Vector.lean:24–28`); `QueryCount.single i := Function.update 0 i 1`
(`V:VCVio/OracleComp/QueryTracking/Structures.lean:321`) is definitionally `Pi.single i 1`
(`M:Algebra/Notation/Pi/Basic.lean:30`), and its 50 consumers redo the `update_self`/`of_ne` case
split that `Pi.single_eq_same/of_ne` and `Finset.sum_pi_single'` (`Piecewise.lean:168`) give.
Medium: `Finset.countP_toList` (`V:…/WithoutReplacement.lean:98`) is proved inline again at
`V:VCVio/OracleComp/ProbComp.lean:377`; `packByte_bitOf_fin` (`fin_cases` over `Fin 256`) is `decide`;
`Fin.mOfFn` is `Vector.ofFnM` (`C:Init/Data/Vector/OfFn.lean:79`) through `arrayVectorEquivFin`.
One row corrected during cross-checking: the data-idiom pass filed "ordered pairs of `Fin n` count"
as a gap after a name-based search; the declaration `Fintype.card_product_filter_lt`
(`M:Data/Fintype/Prod.lean:64`) is exactly `card_filter_fst_lt_snd`, so the Adopt verdict stands —
the "name is a hypothesis" trap, in the direction of false absence.

**Gaps confirmed** (`M:`/`C:`/`B:` grep): `List.cons_injective2`, `Prod.mk.injective2`, `tsum_option`,
`PMF.uniformOfFintype_map_of_bijective`, `FinEnum Bool/ZMod/USize/ISize`, `Sym/Perm/Embedding.finEnum`,
`List.mem_sym` converse, `Fin.mOfFn` (core has `List/Array/Vector.ofFnM` only), `List.countP_eraseIdx_*`,
`BitVec.xor_self_xor`, the `ℝ≥0∞`-cast Gauss sum, `Finset.sum_boole` with a general weight.

### Ring, polynomial, and lattice algebra

**Premise correction.** Upstream `main` has **no** `native_decide` in `LatticeCrypto/`
(`grep` → 0; `scripts/AxiomSweep.lean:90` has `grandfatheredNativeTrust := []`; the committed baseline
has 40 `sorry` and 0 nonstandard axioms). #614 replaced the dense NTT matrix certificates with
structural butterfly stages (`V:LatticeCrypto/Ring/NTTCert.lean:260–596`). Two docstrings still
describe the retired certificate: `V:Extern/MLDSA/NonVacuity.lean:36–38,98` and
`V:Extern/MLDSA/Laws.lean:236` (Adopt: docs fix).

**Correspondence.** `NegacyclicQuotient R n` (`V:LatticeCrypto/Ring/Core.lean:183`, an `abbrev` of
`Polynomial R ⧸ span {X^n + 1}`) *is* `AdjoinRoot (X^n + 1)` (`M:RingTheory/AdjoinRoot.lean:62`),
by `rfl`; nothing in `LatticeCrypto/` imports `AdjoinRoot` (0 hits). `PolyBackend.equivPi` composed
with `ofBackend` is `((AdjoinRoot.powerBasis' hm).basis.reindex _).equivFun`
(`M:RingTheory/AdjoinRoot.lean:633`, typechecks); `ofBackend_injective` (36 lines, `Core.lean:241–276`)
is `AdjoinRoot.modByMonicHom_mk` (`:579`) + `Polynomial.modByMonic_eq_self_iff`. `centeredRepr`
(`V:LatticeCrypto/Ring/Norms.lean:74`) is `ZMod.valMinAbs` character for character
(`M:Data/ZMod/ValMinAbs.lean:23–29`); the file proves `centeredRepr_eq_valMinAbs` (`:139`) and then
restates six `valMinAbs` lemmas on `centeredRepr` (`:78–136` ↔ `natAbs_valMinAbs_le`,
`natAbs_valMinAbs_neg`, `coe_valMinAbs`, `valMinAbs_mem_Ioc`, `valMinAbs_spec`). FIPS rounding ties
`(−α/2, α/2]` are `valMinAbs` on `ZMod α`, **not** `Int.bmod` (which ties the other way for even moduli;
Mathlib has no `bmod` API and no `bmod ↔ valMinAbs` lemma). Norms: `cInfNormOf` has the shape of
`Pi.nnnorm_def'`, `l2NormSqOf` of `EuclideanSpace.norm_sq_eq`; ℕ-valued norms are right for executable
shortness checks, and only `cInfNorm_mul_le` (`Norms.lean:354`, a skew-circulant instance of
`Matrix.linfty_opNorm_mulVec`, `M:Analysis/Matrix/Normed.lean:353`) pays for the missing cast bridge.
`discreteGaussianWeight` is `√(2πσ²) · gaussianPDFReal μ σ² z` (`M:Probability/Distributions/Gaussian/Real.lean:49`);
`ZLattice`/`covolume` have 0 uses, and SIS/LWE are stated as games over matrices, never as lattices.
Matrix conventions are inconsistent: SIS uses `A *ᵥ x` (column), `NoisyLearning` uses `s ᵥ* A` (row),
ML-DSA uses nested-`Vector` `matVecMul`; `PolyMatrix.toMatrix` exists but no proof goes through `Matrix`.

**Integration candidates (verified with `lean_run_code` where marked).**
1. `zeta_pow_256` (48 lines of manual squaring, `V:LatticeCrypto/MLDSA/Concrete/NTT.lean:82–129`),
   `zeta_pow_128` (51 lines, `V:LatticeCrypto/MLKEM/Concrete/NTT.lean:106–156`), both
   `nInv_stageScalar`: one line each by `reduce_mod_char` (`M:Tactic/ReduceModChar.lean`; verified;
   plain `decide` overflows because `ZMod` power is unary). 0 uses of `reduce_mod_char` today.
2. `IsPrimitiveRoot (17 : ZMod 3329) 256`, `IsPrimitiveRoot (1753 : ZMod 8380417) 512`,
   `IsPrimitiveRoot ((11 : ZMod 12289)^6) 2048` in ~10 lines each via `IsPrimitiveRoot.iff_orderOf`,
   `orderOf_eq_of_pow_and_pow_div_prime`, `reduce_mod_char`, `decide` (verified); the generic
   `ζ^n = -1` is `(h.pow _ _).eq_neg_one_of_two_right`. Falcon's `primitiveRoot2N` has no proof at all today.
   0 uses of `IsPrimitiveRoot` in `LatticeCrypto/`.
3. `centeredRepr := ZMod.valMinAbs` and delete the six restated lemmas; restate ML-DSA's
   `power2RoundCoeff`/`decomposeCoeff` low parts as `valMinAbs` on the small modulus so
   `lowBitsCoeff_bound`, `power2RoundCoeff_bound`, `decomposeCoeff_eq`
   (`V:LatticeCrypto/MLDSA/Concrete/Rounding.lean:216–255`) become `natAbs_valMinAbs_le`/`coe_valMinAbs`
   (medium: FIPS-facing definitions).
4. `polyCoeffFinsetSum` (`Core.lean:204–210`) is `Polynomial.finsetSum_coeff` verbatim;
   `ofBackend_injective` via `modByMonicHom`; `vectorNegacyclicRing_instCommRing` (48 lines,
   `V:LatticeCrypto/Ring/SchoolbookCert.lean:260–307`) is `Function.Injective.commRing`
   (`M:Algebra/Ring/InjSurj.lean`); `TransformOps.Laws` (`V:LatticeCrypto/Ring/Transform.lean:254–264`)
   is a `RingEquiv` in disguise (`Equiv.commRing` on `Hat`); the dormant matrix route in
   `NTTCert.lean:58–258` restates `Matrix.mulVec` lemmas — delete rather than port.
5. `decode12Pair_fst/snd` (`V:LatticeCrypto/MLKEM/Concrete/Encoding.lean:510–520`): `omega` alone (verified).
6. Poisson summation `Real.tsum_exp_neg_mul_int_sq` (`M:Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean:123`)
   / `jacobiTheta₂` give the exact theta form of `discreteGaussianSum`, replacing the 106-line
   `le_discreteGaussianSum` (`V:LatticeCrypto/DiscreteGaussian.lean:216–321`) without its `−1` loss and
   opening the deferred smoothing-parameter bound.
7. Pick one matrix convention (Mathlib literature: column `A *ᵥ x`) and route ML-DSA's `TqMatrix`
   through `PolyMatrix.toMatrix` so `mulVec_add`/`mulVec_sub` replace the `Vector`-induction proofs
   (`Transform.lean:306–346`).
8. Make `modulus` an `abbrev` so `reduce_mod_char`/`norm_num` see the literal without the repeated
   `change … ZMod 8380417`.

**NTT trust surface (honest assessment).** What remains trusted is not an axiom but two
`implemented_by` gaps disclosed in the docstrings: the mutable-loop kernels are never shown
extensionally equal to the structural stages, and pointwise multiplication is not verified —
`multiplyNTTs fHat gHat := ntt (negacyclicMul (invNTT fHat) (invNTT gHat))`
(`V:LatticeCrypto/MLDSA/Concrete/NTT.lean:262–264`) makes `toHat_mul` (`:371–373`) tautological,
`loopMultiplyNTTs` is pure `implemented_by`, and Falcon's `Primitives.Laws.transform : NTTRingLaws`
(`V:LatticeCrypto/Falcon/Primitives.lean:297`) is a structure field, i.e. assumed by every
instantiation. Mathlib closes the twiddle half (item 2) and the CRT half
(`Ideal.quotientInfRingEquivPiQuotient`, `Ideal.iInf_span_singleton`, `Polynomial.pairwise_coprime_X_sub_C`,
`Polynomial.quotientSpanXSubCAlgEquiv`, `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`,
`IsPrimitiveRoot.card_nthRoots`; ML-KEM's quadratic factors are `AdjoinRoot (X² − C γ)`). The
un-Mathlib-able part is the Cooley–Tukey bit-reversal lemma "stage output `i` = `eval (ζ^(2·brv i + 1))`":
no `Nat.bitRev`, no FFT anywhere in Mathlib or core (`grep bitRev\|reverseBits` → 0); several hundred
kernel-checked lines over the existing `ButterflyLayout`. `Matrix.det_vandermonde` only certifies
invertibility of a dense evaluation matrix, not the butterfly. Verdict: feasible and worthwhile, the
only route that makes `multiplyNTTs` and the Falcon laws real; record as *track* with the Mathlib
ingredients named.

**Gaps confirmed** (`M:` grep): NTT / negacyclic convolution / skew-circulant (`Matrix.circulant` is
cyclic only), bit reversal, `cyclotomic (2^(k+1)) = X^(2^k) + 1` as a stated lemma (2-line corollary
of `cyclotomic_prime_pow_eq_geom_sum`, verified), `Int.bmod` API and its link to `valMinAbs`, discrete
Gaussians and smoothing parameters on lattices, discrete Young inequality; `Analysis/Fourier/ZMod.lean`
is a complex DFT, not usable for `ZMod q`-valued transforms.

### Tactics and attributes

**Inventory.** Tactic-position counts over the proof libraries (515 files, ≈166k lines, 9546
declarations; median proof 8 lines, 117 proofs over 80 lines): `simp` 6331, `rw` 5107,
`refine … ?_` 1256, `calc` 409, `omega` 464 (`lia` 22), `decide` 219 (no `+kernel`), `grind` 197
plus 67 `@[grind …]` tags (all in `VCVio/EvalDist/`), `unfold` 518 (280 immediately followed by
`simp`/`rw`), `show` 377, `gcongr` ≈110, `positivity` 38, `fun_prop` 8, `measurability` 4,
`finiteness` a handful, `bound` 0. Attributes VCVio has never used: `@[gcongr]`, `@[bound]`,
`@[positivity]`, the `finiteness` rule set, `@[norm_cast]`, `@[mono]` — all 0 (`@[fun_prop]` 3,
`@[ext]` 17 on 234 structures, `@[simps]` 8). Every `mathlibStandardSet` linter is on and fires zero
times, because CI already fails on any non-`sorry` warning; `linter.style.longFile` is off by
default, `docPrime`/`haveLet`/`tacticAnalysis.*` are off.

**Integration candidates (ranked; each is a tagging PR plus a `VCVioTest/Tactic/*.lean` in
`MathlibTest` style — `#guard_msgs`, `guard_target`, `fail_if_success`).**
1. **`gcongr` tagging.** ≈208 hand-written monotonicity steps (`ENNReal.tsum_le_tsum`,
   `mul_le_mul' le_rfl` ×91, `add_le_add le_rfl` ×73, `tsub_le_tsub`, `Finset.sum_le_sum`) sit on heads
   `gcongr` already descends through — VCVio's own working uses at `V:VCVio/EvalDist/Inequalities.lean:85,110`,
   `V:VCVio/EvalDist/TVDist.lean:134`, `V:VCVio/CryptoFoundations/SeededFork.lean:229` prove the descent
   through `∑'`, `*`, `+`, `-`, `/`, `⁻¹`, casts. The recurring blocker: 33 of the
   `refine ENNReal.tsum_le_tsum fun x => ?_` sites are followed by `by_cases hx : x ∈ support mx`
   because the hypothesis is support-restricted. Fix: tag `expectedValue_mono`
   (`V:VCVio/EvalDist/Expectation.lean:66`; its head `expectedValue mx g` has `g` as a direct argument,
   exactly the `Finset.sum_le_sum` shape `gcongr` keys on) and add `expectedValue_mono_of_support`
   (`∀ x ∈ support mx, g x ≤ h x`) plus `probEvent_bind_eq_expectedValue`/`probOutput_bind_eq_expectedValue`
   beside `probEvent_bind_eq_tsum` (`V:VCVio/EvalDist/Monad/Basic.lean:197`); then tag
   `probEvent_mono''` (`V:VCVio/EvalDist/Defs/Basic.lean:949`), `probOutput_bind_mono`/`probEvent_bind_mono`
   (`Monad/Basic.lean:614,648`), `supportWhen_mono` (`V:VCVio/OracleComp/EvalDist.lean:565`),
   `pathwiseCostAtMost_mono`/`queryBoundedAboveBy_mono` (`V:VCVio/OracleComp/QueryTracking/WriterCost.lean:445,654`),
   `expectedQuerySlack_mono`/`probEvent_*_simulateQ_mono` (`V:VCVio/ProgramLogic/Relational/SimulateQ.lean:692,752,2055`).
   Sampled sites: `Monad/Basic.lean:250–265,329–345,488–513,614–622,733–768,840–853`,
   `Monad/Disagreement.lean:52–176`, `IndepProduct.lean:233–254`, `Hops.lean:736–741`,
   `ReplayFork.lean:700–748`, `Unpredictability.lean:205–247`. Expected: 150–250 lines removed and one
   idiom (`gcongr with x hx`) for every bind bound.
2. **`finiteness` tagging.** `probOutput_ne_top`/`probEvent_ne_top`/`probFailure_ne_top`
   (`V:VCVio/EvalDist/Defs/Basic.lean:599,616,625`, already `@[simp, grind .]` and in the preferred
   `≠ ⊤` form) get `@[aesop (rule_sets := [finiteness]) safe apply]` (Mathlib's idiom,
   `M:Data/ENNReal/Basic.lean:366`), likewise `etvDist_ne_top`, `challengeSpaceInv_ne_top`; then the
   46 `ne_top_of_le_ne_top one_ne_top (prob…_le_one)`, 19 `natCast_ne_top`, 34 `mul/add/div_ne_top`
   chains (e.g. `V:Examples/PRFTagReader/MultipleBadCollision.lean:531–552`, `Inequalities.lean:90`,
   `SeededFork.lean:632,665`, six `hDtop` in `Fischlin/KnowledgeSoundness.lean`) become `by finiteness`,
   and hypotheses can use the `(h : c ≠ ⊤ := by finiteness)` autoparam idiom
   (`M:Data/ENNReal/Operations.lean:348`).
3. **`positivity`.** `mul_nonneg (Nat.cast_nonneg _) hε` ×6 (`SimulateQ.lean:1455–1820`),
   `pow_pos (by decide) _` (`MerkleTree/…/QueryBound.lean:37,50`), 43 `Nat.mod_lt _ (by decide)`-style
   goals in ML-KEM/ML-DSA (HashSig already uses `positivity` 17×). Optional ~10-line extensions for
   `OracleComp.tvDist` (used as `abs_nonneg _` at `V:Examples/PRFTagReader/Asymptotic.lean:147–157`)
   and `discreteGaussianWeight/Sum/PMF` (`V:LatticeCrypto/DiscreteGaussian.lean:51,95,122`).
4. **`fun_prop`.** Tag `measurable_dropNoneKernel` (`V:ToMathlib/MeasureTheory/Measure/Option.lean:38`),
   `measurable_none/elim` (`MeasurableSpace/Option.lean:35,65`, `Except.lean:42`),
   `measurable_pullback_answerMap` (`V:VCVio/OracleComp/Coinductive/Responder.lean:244`); replace the
   `Measurable.of_discrete` term proofs at `V:VCVio/EvalDist/Defs/Measure.lean:152,212`,
   `RenyiDiscrete.lean:136,148`. `@[measurability]` merely forwards `Measurable`-shaped lemmas to
   `fun_prop` with a warning (`M:Tactic/Measurability.lean:36–40`): tag `@[fun_prop]` directly.
5. **`push_cast`** for the 37 `rw [… Nat.cast_add, Nat.cast_one …]` sites
   (`Fischlin/KnowledgeSoundness.lean:1722`, `Unpredictability.lean:247`, `MLDSA/Concrete/Rounding.lean:203`,
   `SimulateQ.lean:1463–1467`).
6. **`decide +kernel`** for the 18 `cases ps <;> decide` FIPS-table facts
   (`V:HashSig/SLHDSA/FipsParams.lean:65,71,81`, `Params.lean:272,284`, `MLDSA/Concrete/Rounding.lean:169–172`),
   which otherwise evaluate twice; axiom-free, so compatible with the zero-native-trust rule. Try `cbv`
   on `V:LatticeCrypto/MLKEM/Concrete/Encoding.lean:44–63`; run `linter.tacticAnalysis.omegaToLia` once
   on `Rounding.lean` (53 `omega`).
7. **`grind`.** Tagging stops at `EvalDist/` (the `grind norm` vs `=` choice is documented at
   `V:VCVio/EvalDist/Prod.lean:86`); `grind_pattern` (`C:Init/Grind/Tactics.lean:93–125`) is unused
   although transitivity-shaped `*_mono` lemmas are its textbook case; `[grind hom]` is v4.34. Mathlib's
   `tacticAnalysis.{mergeWithGrind,terminalToGrind}` (`M:Tactic/TacticAnalysis/Declarations.lean:257,285`)
   can be run ad hoc on `simp …; grind` sites (`Prod.lean:136,143`).
8. **`bound`**: low value on `ℝ≥0∞` (its seed set is `ℝ`-centric; only `ofReal_le_ofReal` is tagged);
   `gcongr` covers the same sites.
9. **Structures.** Thin hand-written ext wrappers over existing `@[ext]` lemmas: `spmf_ext`
   (`V:ToMathlib/ProbabilityTheory/OptimalCoupling.lean:110` vs `SPMF.ext`, `SPMF.lean:187`) and
   `poly_ext` (`V:LatticeCrypto/Ring/Kernel.lean:149` vs `PolyBackend.ext_coeff`, `Ring/Core.lean:142`);
   the `unfold` top-25 is dominated by record heads that `@[simps]` would eliminate;
   `deriving Countable` is unused although `Countable` is load-bearing for the measure layer;
   `FipsParameterSet.all`/`all_length` (`V:HashSig/SLHDSA/FipsParams.lean:53`) is what `deriving Fintype`
   + `Fintype.card` give.

**Testing idiom delta.** `MathlibTest` has 2272 `#guard_msgs`, 442 `guard_target`, 191
`fail_if_success`, per-tactic test files; VCVio has 28 `#guard_msgs` and no `guard_target`. Every
tagging PR above should ship its test file; `says` belongs in tests only.

## Integration queue

The reading's findings, ordered by leverage and independence. Each is one PR; none needs a
toolchain bump; none adds CI gating.

| # | PR | Area | What it removes or unlocks |
|---|---|---|---|
| 1 | `gcongr` tagging + `expectedValue_mono_of_support` + `finiteness` rule-set tags, with `VCVioTest/Tactic/` | tactics, `ℝ≥0∞` | ≈200 hand-written monotonicity steps, ≈100 `≠ ⊤` obligations; one idiom for every bind bound |
| 2 | `negligible` ↔ `SuperpolynomialDecay` `toReal`/`ofReal` bridge; `negligible_of_le` via `trans_eventuallyLE`; move the two `_of_poly_bound` lemmas; `tsum_probOutput_mul_le_of_le` | asymptotics | every `ℝ → ℝ≥0∞` crossing by hand; Mathlib's O/o vocabulary on the `toReal` side |
| 3 | `evalDist_mPi = Measure.pi`; `evalDist_bind_const`/`map_const`; `lintegral_countable'_comm` + the discrete measure-bridge simp bundle; measure-side twins of `expectedValue_*` and the Markov bound | probability | the `mul_comm` tail on every bridge; `probOutput_mOfFn`-style proofs; opens `IndepFun`/`HasLaw`/`cond` |
| 4 | Delete the verified duplicates (Adopt table): `FinPairs`, the `General.lean` rows, `Commutative` → `CommApplicative`, `Forall₂`, `LawfulAppend`, `Indexed.lean` copy, `SetM` duplicate normal form, `tsub_le_tsub_add_tsub`, `mod_pow_succ_extract`, `sum_update_*`, `count_toList`, `vector_eq_nil`, `foldlM_range`, `QueryCount.single := Pi.single`, dead cslib import, 0-byte file | constructions (landed with this ledger) | ≈400 lines and one live `Fintype (BitVec n)` instance diamond |
| 5 | `centeredRepr := ZMod.valMinAbs`; `reduce_mod_char` for the twiddle powers; `IsPrimitiveRoot` facts for the three moduli; `polyCoeffFinsetSum`, `ofBackend_injective`, `Function.Injective.commRing`; fix the two stale `native_decide` docstrings | lattice | ≈250 lines; Falcon's root gets a proof; the twiddle half of the NTT trust surface |
| 6 | Generic `[CompleteLattice α] → Lean.Order.CompleteLattice α` bridge; `Prob` lattice via `Set.Iic 1`; `MonadAttach (OracleComp spec)` with `CanReturn := (· ∈ support ·)`; `simulateQ_traverse` via `LawfulTraversable` | control | four hand instances; the first step of the v4.35 `Std.WP` migration; the `mapM`/`forM`/`forIn` lemma trio |
| 7 | HashSig base-w `reverse` bridges to `Nat.digitsAppend`/`ofDigits`; `sum_le_card_nsmul`; `Forall₂` | data idioms | ≈150 lines of re-derived digit arithmetic |
| 8 | cslib-inspired: dependent pairing lemma, finiteness-free `perfectSecrecy ↔ ciphertextRowsEqual`, Shannon `Nat.card K ≥ Nat.card M`; optionally a `SecretSharing` port reusing cslib's Lagrange lemma | crypto foundations | two missing textbook theorems and one missing generic lemma |
| 9 | Prune or `deprecated_module` the 0-reverse-dep `ToMathlib/Control` files; `Examples/{Regev,FrankingProtocol}.lean`; the 30 deprecated aliases; the 23 `BigOperators` opens | hygiene | dead surface |
| 10 | Track items needing design: `QueryCount` monoid leak; cost-layer unification; NTT multiplication laws (twiddle + CRT halves from Mathlib, bit-reversal lemma by hand); Poisson summation for the discrete Gaussian; matrix conventions; selective-expose pilot; `implicit_reducible` canary | design | issues, not sweep PRs |

The tooling table below is deliberately last: nothing in it is urgent, and the maintainer's
guardrails (no native rebuilds on the PR path, no convention gating by script) bound it.

## Tooling

| VCVio | Upstream / sibling | Verdict |
|---|---|---|
| No `testDriver`, no `lintDriver` (`lake check-test`, `lake check-lint` both exit 1) | PolyFun, cslib, Batteries, Mathlib all set both; `lintDriver := "batteries/runLinter"` | **adopt** — test driver as a `@[test_driver] script` that builds the three test libraries and runs the pure-Lean KAT executables; native KATs only under `-- --ffi` |
| Environment linters never run (`simpNF`, `unusedArguments`, `docBlame`, …) | `lake lint` via Batteries | **adopt**, inside the existing build job after the warm rebuild |
| `lean-action@v1` used five times as an elan installer only | v1.6.0 auto-config, `use-mathlib-cache: auto` | **adopt** where it removes hand-rolled steps; never a second full build |
| Eight `lake exe mk_all --lib X --module --check` steps | one regenerate-and-diff script (PolyFun `check-imports.sh`) | **adopt** — bare `lake exe mk_all --check` is unusable here (it iterates `HashSigTest`, the fixtures lib, and non-module `Interop`) |
| `scripts/check-warning-log.py` + 14 path prefixes | `lake build --wfail` | **keep** — the swept libraries carry 40 baseline `sorry` warnings and Lake replays cached warnings, so `--wfail` would need a trace-changing `-Dwarn.sorry=false` and a full local rebuild for every developer |
| `scripts/build_timing_report.sh` + PR-comment automation | Mathlib `bench`/speed-center | **keep** (maintainer decision) |
| `scripts/{pr-summary.py,review.py,requirements.txt}` | `lean4repo-utils@0.3` (`summary.yml`, `review.yml`) | **adopt** — dead, delete |
| `scripts/noshake.json` | `lake shake --keep-implied --keep-prefix` | **track** — nothing runs shake; run manually, keep or delete the config on the evidence |
| Tag-pinned actions | SHA pins + dependabot (PolyFun) | **adopt**; no actionlint/shellcheck/pr-title jobs (no new gating without need) |
| `leanOptions`: `modulesUpperCamelCase`, `style.whitespace` | already implied (`TextBased.lean:560` default; member of `mathlibStandardSet`, `Mathlib/Init.lean:84`) | **adopt** — drop |
| No `moreServerOptions`, no per-library options, no Reservoir metadata | PolyFun, cslib, importGraph | **adopt** — small |
| `Interop/` non-module, excluded from the build | — | **keep** (dormant by design) |
| `downstream_stub_link` job, extern-lib stub archives, isolation ratchets, nightly FFI KATs | no sibling equivalent | **keep** |

## Unused surface

Declarations with no *named* in-repo consumer; instance-providing modules need a synthesis
audit before deletion (see Method).

| Surface | Verdict |
|---|---|
| `ToMathlib/Control/Monad/Commutative.lean` (whole file, ~200 lines) | no consumer; either restate over `CommApplicative` or delete |
| `ToMathlib/Control/Monad/Ordered.lean` `pointwiseRelation`, `Proper` | delete |
| `ToMathlib/General.lean:419,156,165,280` | delete (see Adopt) |
| `Examples/Regev.lean`, `Examples/FrankingProtocol.lean` | delete (fully commented out) |
| `Examples/OneTimePad/Basic.lean:12` `public import Mathlib.Data.Vector.Zip` | no `Vector` use in the file; delete |
| 23 `open (scoped) BigOperators` | the namespace still exists (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`) but the notation is root-level; no-ops |

## Where the queue stands (2026-09-03)

| queue item | PR | note |
|---|---|---|
| 1 `gcongr`/`finiteness` | #636, then #642 | #642 is the smell test: the four `Monad/Disagreement.lean` hop lemmas and four prefix-event bounds re-proved through `expectedValue` + `gcongr`, 22–30 proof lines each down to 6–18 |
| 2 `negligible` bridge | #635 | |
| 3 measure bridge | #637 (reworked), #644, #646 | the `lintegral_countable'_comm` twin was rejected on review and replaced by the one-class `DiscreteEvalDistCompatible` bridge (mass-left by construction, zero `mul_comm`); #644 is the failure measure, #646 `evalDist_mPi = Measure.pi` via `Measure.pi_eq` on boxes |
| 4 duplicates | this PR (#632) | |
| 5 lattice | #634 | |
| 9 hygiene | #647 (C1), #648 (C2) | |
| 10 design track | #650 (transparency policy + expose ratchet), #651 (selective-expose pilot), #653 (program-logic) | the `QueryCount` monoid leak, cost-layer unification, NTT laws, Poisson summation, and matrix conventions remain open |
| tooling | #649 (SHA pins, dependabot, templates), Track A PR (drivers, `check-imports.sh`, dead scripts, options) | `CODEOWNERS` was dropped on review: routing files are boilerplate for a small team |
| gates | #641 | the one-call tactic contract, machine-checked gaps, the `VCVioTest` warning step |

Items 6 (`Lean.Order` bridge, `MonadAttach`, `simulateQ_traverse`), 7 (HashSig digit bridges)
and 8 (cslib-inspired lemmas) are not started.

**Drift census (probed on the built tree for #647, nothing patched).** Nine `simp…; rfl` sites
and 51 norm-then-norm pairs were triaged by the rule in `docs/agents/probability.md` (*Normal
forms and the tactic contract*). Real drift with a known cause: `probOutput_query`'s `rfl`
closes a `Fintype` instance diamond on `spec.Range t` (a `Type`-universe probe closes by `simp`,
the polymorphic statement does not); `probEvent_query` leaves a `DecidablePred` mismatch from
`Classical.decPred` inside `probEvent_liftM_eq_div`; `allOutputsSatisfy_bind` and
`someOutputSatisfies_bind` leave a genuine quantifier swap for `aesop`; the `monad_norm` sandwich
in `Examples/CommitmentScheme/Hiding/LoggingBounds/Average.lean` needs a `StateT.run_*` normal
set. Deliberate, not drift: the `Compatibility.lean` staging of `fs_simp` calls and the ElGamal
inverse-rewrite pair. `open Classical in` needs no change (Mathlib's linter exempts the `in`
form).

## Maintenance

Re-run this survey when the toolchain pin moves. Check, in order: `Init/Control/`, `Std/Do/`
and (from 4.35) `Std/WP/`, `Mathlib/Probability/`, `Mathlib/MeasureTheory/Measure/`,
`Mathlib/Control/`, `Mathlib/Data/FinEnum.lean`, `Cslib/Foundations/`, PolyFun's own ledger.
Re-verify every row; do not diff against this file.
