/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.Fischlin.Defs
import VCVio.CryptoFoundations.Fischlin.CostAccounting
import VCVio.CryptoFoundations.Fischlin.Completeness
import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness

/-!
# Fischlin Transform

This file defines the Fischlin transform (CRYPTO 2005), which converts a Σ-protocol
into a signature scheme (non-interactive proof of knowledge) in the random oracle model
with *online (straight-line) extraction*.

Unlike the Fiat-Shamir transform, which requires a rewinding extractor (via the forking lemma),
the Fischlin transform enables extraction by simply observing the prover's hash queries.
This comes at the cost of a more complex prover that performs a "proof-of-work" search
over the challenge space, and a slight completeness error.

## Parameters

* `ρ` — number of parallel repetitions
* `b` — hash output bit-length (random oracle range is `Fin (2^b)`)
* `S` — maximum allowed sum of hash values in a valid proof (paper notation)

## Module layout

The development is split across the sibling modules under `Fischlin/`:

* `Fischlin.Defs` — the random-oracle input type, oracle signature, proof type, the
  prover search `fischlinSearchAux`, the transform `Fischlin`, and the `runtime` bundle.
* `Fischlin.CostAccounting` — random-oracle query-cost and expected-query bounds for
  `sign` and `verify`.
* `Fischlin.Completeness` — the completeness bound `almostComplete` via the pure-probability
  model game.
* `Fischlin.KnowledgeSoundness` — online extraction and the `knowledgeSoundness` bound via a
  supermartingale potential argument.

## References

* Marc Fischlin, "Communication-Efficient Non-Interactive Proofs of Knowledge
  with Online Extractors", CRYPTO 2005.
-/
