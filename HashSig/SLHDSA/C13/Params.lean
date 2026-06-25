/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Params

/-!
# C13 parameter set (WOTS+C / FORS+C, keccak256)

C13 is the EVM-optimized SLH-DSA-family variant from the `SPHINCs-` research repo
(`src/SPHINCs-C13Asm.sol`), built on the C-series compact primitives of ePrint 2025/2203:

- **WOTS+C** — drops the Winternitz checksum chains and instead grinds a 32-bit counter (stored
  per hypertree layer in the signature) so the `l = 43` base-`w` digits of the WOTS message sum
  to a fixed `targetSum = 208`. Forward-only forgery is blocked by the fixed-sum
  incomparability (the same combinatorial core as `SLHDSA.WotsChecksum`, specialized to a
  constant sum).
- **FORS+C** — grinds the message randomizer so the *last* (`k`-th) FORS tree's leaf index is
  forced to `0`; that tree's auth path is omitted (`k − 1` trees carry auth paths, all `k`
  reveal a leaf secret).
- **d = 2** hypertree of height `h = 22` (two XMSS layers of height `h' = 11`).
- **keccak256** (truncated to `n = 16`) over the FIPS 205 §11.2.2 *uncompressed* 32-byte `ADRS`,
  with a single domain-separated `H_msg = keccak256(seed ‖ root ‖ R ‖ msg ‖ 0xFF·32)` (no MGF1).

This module fixes the parameters and the **C13-specific** byte sizes (the FIPS size formulas in
`SLHDSA.Params` do **not** apply: WOTS+C has no checksum chains, and FORS+C omits one auth
path). The remaining C13 build-out — a `WotsC` module (counter-mixed digits + fixed-sum gate),
a `ForsC` module (forced-zero last tree), the `d = 2` hypertree fold, the keccak/32-byte-ADRS
`Primitives` instantiation, and verification against `SPHINCs-C13Asm.sol` / the `signer-wasm`
KAT — reuses the shared `SLHDSA.Merkle` core and the `SLHDSA.WotsChecksum` incomparability lemma.

## References

- The SPHINCs- research repo: `src/SPHINCs-C13Asm.sol`, `SECURITY-REVIEW-C13-SLHDSA.md`
- ePrint 2025/2203 (the C-series WOTS+C and FORS+C primitives), NIST FIPS 205 §11.2.2
-/


namespace SLHDSA.C13

open SLHDSA

/-- The C13 numeric parameters (shared `Params` shape: `w = 2^lgw = 8`, `h' = h/d = 11`). -/
def params : Params := { n := 16, h := 22, d := 2, hp := 11, a := 19, k := 7, lgw := 3 }

/-- WOTS+C target digit-sum: the `l` base-`w` WOTS digits must sum to exactly this. -/
def targetSum : ℕ := 208

/-- Number of WOTS+C chains (no checksum chains; `l = ⌈8n/lgw⌉ = 43`). -/
def wotsLen : ℕ := 43

/-- FORS+C signature bytes: `k` revealed leaf secrets plus `(k−1)` auth paths
(the forced-zero `k`-th tree carries no auth path). -/
def forsBytes : ℕ := params.k * params.n + (params.k - 1) * params.a * params.n

/-- Bytes of one hypertree layer: WOTS+C signature `l·n`, the 32-bit counter, and the XMSS
auth path `h'·n`. -/
def htLayerBytes : ℕ := wotsLen * params.n + 4 + params.hp * params.n

/-- Total C13 signature size: `R(n) ‖ SIG_FORS+C ‖ d × layer`. -/
def signatureBytes : ℕ := params.n + forsBytes + params.d * htLayerBytes

/-- Public-key size `2n` and secret-key size `4n` (as FIPS 205). -/
def publicKeyBytes : ℕ := 2 * params.n
def secretKeyBytes : ℕ := 4 * params.n

/-- The documented C13 sizes are consistent: signature is 3688 bytes, pk 32, sk 64,
and the WOTS+C chain count is `⌈8n/lgw⌉`. -/
theorem c13_sizes :
    signatureBytes = 3688 ∧ publicKeyBytes = 32 ∧ secretKeyBytes = 64 ∧
      wotsLen = params.len1 := by
  decide

end SLHDSA.C13
