# SymmEncAlg Redesign

**Status**: Planned (not yet started)

## Problem

`SymmEncAlg` in `VCVio/CryptoFoundations/SymmEncAlg.lean` extends `OracleContext Q ProbComp` and uses `ℕ`-indexed type families, making it structurally different from every other scheme struct in the codebase.

All other scheme structs (`SignatureAlg`, `KEMScheme`, `AsymmEncAlg`, `MacAlg`, `DEMScheme`) are parameterized by `(m : Type -> Type u) [Monad m]` with plain `Type` parameters.
This inconsistency prevents `SymmEncAlg` from participating in the `HasQuery` capability story.

## Current consumer

Only `Examples/OneTimePad.lean` instantiates `SymmEncAlg`.

## Proposed redesign

1. Make `SymmEncAlg` monad-generic like the other scheme structs: parameterize by `(m : Type -> Type u) [Monad m]` with plain `Type` parameters for key, plaintext, and ciphertext spaces.
2. Optionally keep an indexed wrapper (analogous to `AsymptSecExp`) for asymptotic security statements that need `ℕ`-indexed families.
3. Move `OracleContext` dependency to the game/experiment level rather than the scheme struct itself.
4. Update `Examples/OneTimePad.lean` to use the new definition.
