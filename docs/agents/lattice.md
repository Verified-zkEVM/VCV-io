# LatticeCrypto Layout and Workflows

## What Lives Where

The lattice stack is split into five layers:

- `LatticeCrypto/`: generic lattice algebra, hardness assumptions, scheme specs, security theorems, and FFI-free executable concrete implementations.
- `Extern/`: the native FFI surface — `@[extern]` bindings (`Extern/Hashing.lean`, `Extern/*/FFI.lean`) and every FFI-backed module reaching them (sampling, instances, and for Falcon also FFT/keygen/signing). No proof library may import it.
- `LatticeCryptoTest/`: ACVP vectors, randomized regression tests, and differential checks against native reference code.
- `csrc/`: small C shims that expose the native ML-DSA, ML-KEM, and Falcon implementations to Lean.
- `third_party/`: native backends as git submodules; when absent, the native `extern_lib` targets build as empty stubs.

Use `VCVio/` when you are changing framework abstractions such as `SignatureAlg`, `IdenSchemeWithAbort`, `GPVHashAndSign`, or `FujisakiOkamoto`. Use `LatticeCrypto/` when you are instantiating those abstractions for a lattice scheme.

## Core Entry Points

### Shared algebra and utilities

- `LatticeCrypto/Ring/Core.lean`: `PolyBackend`, `PolyVec`, `PolyMatrix`, `NegacyclicQuotient`.
- `LatticeCrypto/Ring/Kernel.lean`: `PolyKernel`, `NegacyclicRing`, `NegacyclicRingSemantics`, schoolbook multiplication.
- `LatticeCrypto/Ring/VectorBackend.lean`: canonical vector-backed instantiation.
- `LatticeCrypto/Ring/Transform.lean`: `TransformPoly`, `TransformOps`, and transform laws.
- `LatticeCrypto/Ring/Sampling.lean`: `SampleableType` instances for `backend.Poly` and `TransformPoly`, so `$ᵗ Rq` / `$ᵗ Tq` (and the `RqVec` / `TqMatrix` vectors) work for any scheme whose coefficient type is sampleable.
- `LatticeCrypto/Ring/Norms.lean`: centered representatives, `NormOps`, and generic norm infrastructure.
- `LatticeCrypto/Ring/Rounding.lean`: abstract `RoundingOps` and `Power2RoundOps` used by ML-DSA.
- `LatticeCrypto/Ring/IntegralLift.lean`: `IntegralLift` for Falcon integer-polynomial arithmetic.
- `LatticeCrypto/Ring/NTTCert.lean`: shared matrix scaffolding plus structural butterfly layouts,
  stage composition, normalization, and coefficient-backend lifts for concrete NTT certificates.
- `LatticeCrypto/DiscreteGaussian.lean`: generic discrete Gaussian support used by Falcon.

### Hardness assumptions

- `LatticeCrypto/HardnessAssumptions/LearningWithErrors.lean`: the generic LWE / MLWE problem surfaces used by ML-KEM.
- `LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`: SIS and self-target variants used by ML-DSA and Falcon-style arguments.

### ML-DSA

- `LatticeCrypto/MLDSA/Params.lean`: parameter sets and byte sizes.
- `LatticeCrypto/MLDSA/Arithmetic.lean`: ML-DSA-specific arithmetic assembly, vectors, and NTT-facing types.
- `LatticeCrypto/MLDSA/Primitives.lean`: abstract hashing, sampling, rounding, and encoding-facing operations.
- `LatticeCrypto/MLDSA/Scheme.lean`: proof-level identification scheme with aborts.
- `LatticeCrypto/MLDSA/Signature.lean`: FIPS-style signing and verification layer built on the proof-level scheme.
- `LatticeCrypto/MLDSA/Security.lean`: reduction statements from the signature / IDS surfaces to underlying assumptions.
- `LatticeCrypto/MLDSA/SecurityNMA.lean`: the no-message-attack chain, with the key swap modelled over short-box MLWE.
- `LatticeCrypto/MLDSA/Concrete/`: executable implementations of NTT, rounding, and encoding, plus
  `LawBounds.lean` — the algebraic range and bit-width bounds behind the `Primitives.Laws` fields.
- `Extern/MLDSA/`: FFI bindings, SHAKE-backed sampling, and the FFI-backed instance. `Laws.lean`
  discharges the `Primitives.Laws` fields that mention `concretePrimitives`, and `NonVacuity.lean`
  banks the `seedRevealingPrims` inhabitance witness for `Primitives.Laws`.

### ML-KEM

- `LatticeCrypto/MLKEM/Params.lean`: parameter sets and ciphertext / key dimensions.
- `LatticeCrypto/MLKEM/Arithmetic.lean`: ML-KEM arithmetic assembly and vector types.
- `LatticeCrypto/MLKEM/Primitives.lean`: abstract sampling, hashing, and encoding-facing operations.
- `LatticeCrypto/MLKEM/KPKE.lean`: public-key encryption layer.
- `LatticeCrypto/MLKEM/Internal.lean`: deterministic internal algorithms following the FIPS decomposition.
- `LatticeCrypto/MLKEM/KEM.lean`: top-level checked KEM interface.
- `LatticeCrypto/MLKEM/Security.lean`: IND-CPA and IND-CCA theorem surfaces.
- `LatticeCrypto/MLKEM/Concrete/`: executable CBD, encoding, and NTT. `concreteEncoding` uses
  `ByteArray` for every encoded component; the `DecidableEq` instances the generic KEM entry
  points require are stated on its projections (`(concreteEncoding params).EncodedTHat` /
  `EncodedU` / `EncodedV`), so no local instances are needed downstream. Encoder output sizes
  are named laws (`concreteEncoding_byteEncode12Vec_size`, `concreteEncoding_byteEncodeDUVec_size`,
  `concreteEncoding_byteEncodeDV_size`) tied to `Params.publicKeyBytes` / `Params.ciphertextBytes`.
- `Extern/MLKEM/`: FFI bindings and the FFI-backed instance wiring. The per-parameter aliases
  `mlkem512Encoding` / `mlkem768Encoding` / `mlkem1024Encoding` are `abbrev`s so the generic
  `concreteEncoding` instances resolve through them; `LatticeCryptoTest/MLKEM/Helpers.lean`
  carries build-time canaries for that path.

### Falcon

- `LatticeCrypto/Falcon/Params.lean`: scheme constants.
- `LatticeCrypto/Falcon/Arithmetic.lean`: Falcon arithmetic assembly and integer-polynomial infrastructure.
- `LatticeCrypto/Falcon/Primitives.lean`: abstract primitive operations such as sampling, hashing, and compression.
- `LatticeCrypto/Falcon/Scheme.lean`: scheme semantics and the GPV bridge.
- `LatticeCrypto/Falcon/Security.lean`: high-level security statements.
- `LatticeCrypto/Falcon/Concrete/`: executable NTT, floating-point emulation (FPR/FXR), encodings, and the NTRU solver.
- `Extern/Falcon/`: FFI bindings plus the SHAKE-backed sampler, FFT, keygen, signing, and instance layers.

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
- executable arithmetic or codec behavior: start in `Concrete/`; FFI-backed sampling, instances, and Falcon FFT/keygen/signing live under `Extern/`
- native differential tests or vector failures: start in `LatticeCryptoTest/` and then follow the import chain into `Extern/`, `Concrete/`, or `csrc/`
- generic security-game surfaces: start in `VCVio/CryptoFoundations/`

## Common Gotchas

- Keep the proof-level and executable layers distinct. `Scheme.lean` is usually the semantic model; `Concrete/` and `Extern/` files are the executable realization (the FFI-touching parts under `Extern/`).
- ML-DSA has both an identification-scheme layer and a FIPS signing layer. Changes to challenge formation, abort conditions, or rounding often need updates in both `Scheme.lean` and `Signature.lean`.
- ML-KEM separates K-PKE, deterministic internal algorithms, and the top-level checked KEM wrapper. Put changes at the lowest layer that matches the semantics you need.
- Falcon uses GPV-style abstractions at the proof layer and FFT / FPR machinery at the executable layer. Do not mix those concerns unless you are explicitly proving the bridge.
- Differential tests rely on `csrc/` and `third_party/`. If a pure Lean change breaks only those tests, check for serialization, endian, or fixed-size input mismatches before touching the mathematical layer.
