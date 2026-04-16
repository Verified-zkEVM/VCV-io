/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.Sigma.Security
import VCVio.CryptoFoundations.FiatShamir.WithAbort
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Cost
import VCVio.CryptoFoundations.FiatShamir.WithAbort.ExpectedCost
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security

/-!
# Fiat-Shamir transform

Top-level import for both variants of the Fiat-Shamir transform used by the
repo's signature schemes:

- **Σ-protocol variant** (`FiatShamir.Sigma*`): non-aborting 3-round Fiat-Shamir.
- **With-aborts variant** (`FiatShamir.WithAbort*`): retry-loop Fiat-Shamir
  used by lattice schemes such as ML-DSA.

Callers that only need part of the interface may import the specific
submodule instead; this umbrella exists to keep common entry points
(correctness, EUF-CMA security) addressable from a single import.
-/
