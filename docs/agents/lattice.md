# LatticeCrypto Layout and Workflows

## What Lives Where

The lattice stack is split into four layers:

- `LatticeCrypto/`: generic lattice algebra, hardness assumptions, scheme specs, security theorems, and executable concrete implementations.
- `LatticeCryptoTest/`: ACVP vectors, randomized regression tests, and differential checks against native reference code.
- `csrc/`: small C shims that expose the native ML-DSA, ML-KEM, and Falcon implementations to Lean.
- `third_party/`: vendored native backends used by the FFI and test harnesses.

Use `VCVio/` when you are changing framework abstractions such as `SignatureAlg`, `IdenSchemeWithAbort`, `GPVHashAndSign`, or `FujisakiOkamoto`. Use `LatticeCrypto/` when you are instantiating those abstractions for a lattice scheme.

## Core Entry Points

### Shared algebra and utilities

- `LatticeCrypto/Norm.lean`: centered representatives and norm lemmas.
- `LatticeCrypto/Ring.lean`: common ring-level infrastructure shared across schemes.
- `LatticeCrypto/Rounding.lean`: abstract rounding interfaces and laws used by ML-DSA.
- `LatticeCrypto/DiscreteGaussian.lean`: generic discrete Gaussian support used by Falcon.

### Hardness assumptions

- `LatticeCrypto/HardnessAssumptions/LearningWithErrors.lean`: the generic LWE / MLWE problem surfaces used by ML-KEM.
- `LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`: SIS and self-target variants used by ML-DSA and Falcon-style arguments.

### ML-DSA

- `LatticeCrypto/MLDSA/Params.lean`: parameter sets and byte sizes.
- `LatticeCrypto/MLDSA/Ring.lean`: ML-DSA-specific rings, vectors, and NTT-facing types.
- `LatticeCrypto/MLDSA/Primitives.lean`: abstract hashing, sampling, rounding, and encoding-facing operations.
- `LatticeCrypto/MLDSA/Scheme.lean`: proof-level identification scheme with aborts.
- `LatticeCrypto/MLDSA/Signature.lean`: FIPS-style signing and verification layer built on the proof-level scheme.
- `LatticeCrypto/MLDSA/Security.lean`: reduction statements from the signature / IDS surfaces to underlying assumptions.
- `LatticeCrypto/MLDSA/Concrete/`: executable implementations of NTT, sampling, rounding, encoding, and FFI-backed instances.

### ML-KEM

- `LatticeCrypto/MLKEM/Params.lean`: parameter sets and ciphertext / key dimensions.
- `LatticeCrypto/MLKEM/Ring.lean`: ML-KEM ring and vector types.
- `LatticeCrypto/MLKEM/Primitives.lean`: abstract sampling, hashing, and encoding-facing operations.
- `LatticeCrypto/MLKEM/KPKE.lean`: public-key encryption layer.
- `LatticeCrypto/MLKEM/Internal.lean`: deterministic internal algorithms following the FIPS decomposition.
- `LatticeCrypto/MLKEM/KEM.lean`: top-level checked KEM interface.
- `LatticeCrypto/MLKEM/Security.lean`: IND-CPA and IND-CCA theorem surfaces.
- `LatticeCrypto/MLKEM/Concrete/`: executable CBD, encoding, NTT, FFI, and instance wiring.

### Falcon

- `LatticeCrypto/Falcon/Params.lean`: scheme constants.
- `LatticeCrypto/Falcon/Ring.lean`: Falcon ring types and integer-polynomial infrastructure.
- `LatticeCrypto/Falcon/Primitives.lean`: abstract primitive operations such as sampling, hashing, and compression.
- `LatticeCrypto/Falcon/Scheme.lean`: scheme semantics and the GPV bridge.
- `LatticeCrypto/Falcon/Security.lean`: high-level security statements.
- `LatticeCrypto/Falcon/Concrete/`: executable FFT, NTT, floating-point emulation, keygen, sampling, signing, and FFI support.

## How It Connects To `VCVio`

The lattice schemes are not standalone frameworks. They reuse the generic cryptographic interfaces in `VCVio/CryptoFoundations`:

- ML-DSA instantiates `IdenSchemeWithAbort` and `FiatShamirWithAbort`.
- Falcon instantiates `GPVHashAndSign` and `GenerableRelation`.
- ML-KEM uses the generic `AsymmEncAlg`, `KEMScheme`, and Fujisaki-Okamoto security surfaces.

If a change affects both the generic abstraction and a lattice instantiation, update both sides in one pass. Do not leave compatibility shims behind.

## Picking the Right File

When the task is about:

- proof-level semantics or reduction statements: start in `Scheme.lean` or `Security.lean`
- FIPS algorithm structure: start in `Signature.lean`, `KEM.lean`, or `Internal.lean`
- executable arithmetic or codec behavior: start in `Concrete/`
- native differential tests or vector failures: start in `LatticeCryptoTest/` and then follow the import chain into `Concrete/` or `csrc/`
- generic security-game surfaces: start in `VCVio/CryptoFoundations/`

## Common Gotchas

- Keep the proof-level and executable layers distinct. `Scheme.lean` is usually the semantic model; `Concrete/` files are the executable realization.
- ML-DSA has both an identification-scheme layer and a FIPS signing layer. Changes to challenge formation, abort conditions, or rounding often need updates in both `Scheme.lean` and `Signature.lean`.
- ML-KEM separates K-PKE, deterministic internal algorithms, and the top-level checked KEM wrapper. Put changes at the lowest layer that matches the semantics you need.
- Falcon uses GPV-style abstractions at the proof layer and FFT / FPR machinery at the executable layer. Do not mix those concerns unless you are explicitly proving the bridge.
- Differential tests rely on `csrc/` and `third_party/`. If a pure Lean change breaks only those tests, check for serialization, endian, or fixed-size input mismatches before touching the mathematical layer.
