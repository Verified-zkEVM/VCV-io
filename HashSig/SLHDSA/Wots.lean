/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Primitives
import HashSig.SLHDSA.Encoding
import HashSig.SLHDSA.WotsChecksum

/-!
# WOTS+ (FIPS 205 §5)

The Winternitz one-time signature over the abstract `Primitives` bundle: the hash chain
(`chain`, Alg 5), public-key generation (`wotsPkGen`, Alg 6), signing (`wotsSign`, Alg 7), and
public-key recovery from a signature (`wotsPkFromSig`, Alg 8). Signatures are length-indexed
`Vector`s of `len` nodes, so per-chain indexing is total.

The headline result is `wotsPkFromSig_wotsSign`: recovering the public key from an honest
signature reproduces `wotsPkGen`. Its only ingredient is the hash-chain composition law
`chain_compose`, proved by induction with no hash hypotheses — the deterministic core that
drives XMSS/hypertree correctness downstream.

## References

- NIST FIPS 205, §5 (Algorithms 5–8), §5.4 (the checksum, validated in `WotsChecksum`)
-/


namespace SLHDSA

open WotsChecksum

variable {p : Params}

/-- `0 < w = 2^lgw`. -/
theorem Params.w_pos (p : Params) : 0 < p.w := by
  unfold Params.w; positivity

/-! ### The hash chain (FIPS 205 Algorithm 5) -/

/-- `chain(X, i, s, PK.seed, ADRS)`: apply `F` `s` times to `X`, starting at hash index `i`
(the `j`-th step uses hash address `i + j`). Structural recursion on the step count. -/
def chain (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y)
    (i : ℕ) : ℕ → prims.Y
  | 0 => x
  | s + 1 => prims.F pkSeed (adrs.setHashAddress (i + s)) (chain prims pkSeed adrs x i s)

/-- Hash-chain composition: chaining `a` steps then `b` more (from index `i + a`) equals
chaining `a + b` steps from `i`. The deterministic backbone of WOTS+ correctness. -/
theorem chain_compose (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i a b : ℕ) :
    chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b
      = chain prims pkSeed adrs x i (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change prims.F pkSeed (adrs.setHashAddress (i + a + b))
          (chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b)
        = prims.F pkSeed (adrs.setHashAddress (i + (a + b)))
          (chain prims pkSeed adrs x i (a + b))
    rw [ih, Nat.add_assoc]

/-! ### WOTS+ addresses -/

/-- Address for deriving the secret value of chain `i` (type `WOTS_PRF`, keypair preserved). -/
def wotsSkAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsPrf).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Base address for the `F`-steps of chain `i` (type `WOTS_HASH`, chain address `i`). -/
def wotsChainAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  (adrs.setTypeAndClear .wotsHash).setChainAddress i

/-- Address for compressing the `len` chain ends into the WOTS public key (type `WOTS_PK`). -/
def wotsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .wotsPk).setKeyPairAddress adrs.getKeyPairAddress

/-! ### Message-to-digit derivation (FIPS 205 §5.2–5.4) -/

/-- The `len1` base-`w` message digits of the node being signed. -/
def wotsMsgDigits (prims : Primitives p) (msg : prims.Y) : List ℕ :=
  base2b (prims.yToBytes msg).toList p.lgw p.len1

/-- The full step-count list: message digits followed by the base-`w` checksum digits; length
`len`. -/
def chainLengths (prims : Primitives p) (msg : prims.Y) : List ℕ :=
  wotsFullDigits (wotsMsgDigits prims msg) p.w p.len1 p.len2

/-- Every entry of `chainLengths` is a genuine base-`w` digit (`< w`). -/
theorem chainLengths_mem_lt (prims : Primitives p) (msg : prims.Y) :
    ∀ d ∈ chainLengths prims msg, d < p.w := by
  intro d hd
  unfold chainLengths wotsFullDigits at hd
  rcases List.mem_append.mp hd with h | h
  · have hb := base2b_lt (prims.yToBytes msg).toList p.lgw p.len1 d h
    rwa [Params.w]
  · exact digitsOfBaseW_lt _ p.w p.len2 (Params.w_pos p) d h

/-- The step count of chain `i`: the `i`-th entry of `chainLengths` (`0` past the end). -/
def chainSteps (prims : Primitives p) (msg : prims.Y) (i : ℕ) : ℕ :=
  (chainLengths prims msg).getD i 0

theorem chainSteps_lt (prims : Primitives p) (msg : prims.Y) (i : ℕ) :
    chainSteps prims msg i < p.w := by
  unfold chainSteps
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i (chainLengths prims msg).length with h | h
  · rw [List.getElem?_eq_getElem h]
    simpa using chainLengths_mem_lt prims msg _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]
    simpa using Params.w_pos p

theorem chainSteps_le (prims : Primitives p) (msg : prims.Y) (i : ℕ) :
    chainSteps prims msg i ≤ p.w - 1 :=
  Nat.le_sub_one_of_lt (chainSteps_lt prims msg i)

/-! ### Public-key generation, signing, and recovery -/

/-- A WOTS+ signature: the `len` chain values, length-indexed. -/
abbrev WotsSig (p : Params) (prims : Primitives p) := Vector prims.Y p.len

/-- The `len` chain ends of the WOTS+ public key (chain every secret value to the top, `w-1`). -/
def wotsPkGenTops (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Vector prims.Y p.len :=
  Vector.ofFn fun i : Fin p.len =>
    chain prims pk (wotsChainAdrs adrs i.val) (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1)

/-- WOTS+ public-key generation (FIPS 205 Algorithm 6). -/
def wotsPkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  prims.Tl pk (wotsPkAdrs adrs) (wotsPkGenTops prims sk pk adrs).toList

/-- WOTS+ signing (FIPS 205 Algorithm 7): chain each secret value to its message height. -/
def wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : WotsSig p prims :=
  Vector.ofFn fun i : Fin p.len =>
    chain prims pk (wotsChainAdrs adrs i.val) (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0
      (chainSteps prims msg i.val)

/-- The `len` chain ends recovered from a signature (complete each chain from its message height
to the top). -/
def wotsPkFromSigTops (prims : Primitives p) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : Vector prims.Y p.len :=
  Vector.ofFn fun i : Fin p.len =>
    chain prims pk (wotsChainAdrs adrs i.val) sig[i.val] (chainSteps prims msg i.val)
      (p.w - 1 - chainSteps prims msg i.val)

/-- WOTS+ public-key recovery from a signature (FIPS 205 Algorithm 8). -/
def wotsPkFromSig (prims : Primitives p) (sig : WotsSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  prims.Tl pk (wotsPkAdrs adrs) (wotsPkFromSigTops prims sig msg pk adrs).toList

/-! ### Correctness -/

/-- Recovering the chain ends from an honest signature reproduces the public-key chain ends. -/
theorem wotsPkFromSigTops_wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigTops prims (wotsSign prims msg sk pk adrs) msg pk adrs
      = wotsPkGenTops prims sk pk adrs := by
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops, wotsPkGenTops, wotsSign, Vector.getElem_ofFn]
  have hc := chain_compose prims pk (wotsChainAdrs adrs i)
    (prims.PRF pk sk (wotsSkAdrs adrs i)) 0 (chainSteps prims msg i)
    (p.w - 1 - chainSteps prims msg i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (chainSteps_le prims msg i)]

/-- **WOTS+ correctness** (FIPS 205, Algorithms 6–8): recovering the public key from an honest
signature reproduces `wotsPkGen`. -/
theorem wotsPkFromSig_wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSig prims (wotsSign prims msg sk pk adrs) msg pk adrs
      = wotsPkGen prims sk pk adrs := by
  unfold wotsPkFromSig wotsPkGen
  rw [wotsPkFromSigTops_wotsSign]

end SLHDSA
