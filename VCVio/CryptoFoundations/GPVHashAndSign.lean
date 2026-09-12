/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.Basic
public import VCVio.CryptoFoundations.GPVHashAndSign.MinEntropy
public import VCVio.CryptoFoundations.GPVHashAndSign.CollisionTelescope
public import VCVio.CryptoFoundations.GPVHashAndSign.Factorization
public import VCVio.CryptoFoundations.GPVHashAndSign.GameRuns
public import VCVio.CryptoFoundations.GPVHashAndSign.TapeFactorization
public import VCVio.CryptoFoundations.GPVHashAndSign.FlagHandlers
public import VCVio.CryptoFoundations.GPVHashAndSign.CombinedHandler
public import VCVio.CryptoFoundations.GPVHashAndSign.GameIdentification
public import VCVio.CryptoFoundations.GPVHashAndSign.VerificationBridge
public import VCVio.CryptoFoundations.GPVHashAndSign.TrapCount
public import VCVio.CryptoFoundations.GPVHashAndSign.EmbedIndex
public import VCVio.CryptoFoundations.GPVHashAndSign.Security
public import VCVio.CryptoFoundations.GPVHashAndSign.AppendQuery
public import VCVio.CryptoFoundations.GPVHashAndSign.SamplerTransport

/-!
# GPV Hash-and-Sign Framework

This file defines a generic hash-and-sign signature scheme following the GPV (Gentry–Peikert–
Vaikuntanathan) framework [GPV08]. The construction is parameterized by a *preimage sampleable
function* (PSF), a many-to-one function equipped with a probabilistic trapdoor that samples
short preimages.

The GPV framework is the hash-and-sign analogue of the Fiat-Shamir transform:

| Interactive protocol | Fiat-Shamir → SignatureAlg |
|---|---|
| Trapdoor PSF | GPVHashAndSign → SignatureAlg |

## Main Definitions

- `PreimageSampleableFunction` — a function `eval` with a probabilistic trapdoor sampler and a
  shortness predicate on preimages.
- `GPVHashAndSign` — builds a `SignatureAlg` in the random-oracle model from a PSF, a generable
  key relation, and a salt type.

## Security

The PFDH (Probabilistic Full-Domain Hash) variant of the GPV scheme uses a random salt per
signing query. The precise EUF-CMA bound from [FGdG+25] Theorem 1 is:

  `Adv^{UF-CMA}(A) ≤ (r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS}(B))^{...})^{...}`
  `                  + tail_bound + Q_s · (C_s + Q_H) / 2^k`

where the salt-collision term `Q_s · (C_s + Q_H) / 2^k` bounds the probability that
a fresh salt collides with any prior RO query. The constant the formalized statements prove is
the closed birthday form `(qSign + qHash)² / (2 · |Salt|)` (`GPVHashAndSign.collisionBound`),
counting every salt appearing in a signing or random-oracle query. The underlying telescope
establishes the exact union sum `∑_{j < qSign} (j + qHash) / |Salt|`
(`GPVHashAndSign.sum_range_div_card_le_collisionBound`); the closed form is looser than that sum
by the `qHash² / 2` term, which dominates when `qHash ≫ qSign`, and is negligible for Falcon's
320-bit salts at any realistic budget. GPV08 Proposition 6.2 itself only sketches the
same-message salt reuse term `Q_sign² / 2^k`.

The proof decomposes into:
- `GPVHashAndSign.reduction`: the collision-finding adversary (sign-then-hash simulation)
- `GPVHashAndSign.programmedPreimageReduction`: the exact-match branch reduction
- `GPVHashAndSign.collisionBound`: the salt-collision birthday bound
- `GPVHashAndSign.forgery_yields_collision`: the core distinct-preimage game-hop
- `GPVHashAndSign.forgery_yields_collision_or_exact_match`: the explicit split bound

## Public endpoints

- `GPVHashAndSign.euf_cma_split_bound_of_queryBound`: the split bound (collision term,
  exact-match term, salt-collision term) for every adversary obeying the query bound.
- `GPVHashAndSign.euf_cma_collision_bound_of_queryBound`: the closed collision-style bound, with
  the exact-match term priced by the trapdoor guessing probability.

Both discharge the random-oracle convention `ForgesQueriedPoint` by the append-forgery-query
compiler at one extra hash query; the `ForgesQueriedPoint`-hypothesis forms
`GPVHashAndSign.euf_cma_split_bound` / `GPVHashAndSign.euf_cma_collision_bound` are the
primitives they chain through.

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769. First concrete proof for Falcon+ (Theorem 1).
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Tightens Rényi loss to < 0.2 bits.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- BDF+11: Boneh et al. "Random Oracles in a Quantum World." ASIACRYPT 2011.

## Module layout

The development is split along its proof phases: `Basic` (the PSF abstraction and
the scheme), `MinEntropy` (the guessing-probability bound for the programmed-preimage
experiment), `CollisionTelescope`, `Factorization`, `GameRuns`, `TapeFactorization`,
`FlagHandlers`, `CombinedHandler`, `GameIdentification`, `VerificationBridge`,
`TrapCount`, `EmbedIndex`, `Security` (the headline EUF-CMA bounds),
`AppendQuery` (the append-forgery-query compiler discharging `ForgesQueriedPoint`), and
`SamplerTransport` (the adaptive trapdoor-sampler-swap accumulation).
This umbrella module re-exports all of them.
-/

@[expose] public section
