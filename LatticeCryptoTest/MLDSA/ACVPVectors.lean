/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCryptoTest.MLDSA.Helpers

/-!
# ML-DSA-65 Test Vectors

Keygen vectors originate from the NIST ACVP server
(https://github.com/usnistgov/ACVP-Server, ML-DSA-keyGen-FIPS204).

Signing vectors specify a keygen seed and a message. The test generates keys from the seed,
signs the message with both Lean and mldsa-native (deterministic, `rnd = 0`), and compares the
results byte-exactly.
-/


namespace MLDSA.Test.ACVP

/-! ## Key generation vectors (ML-DSA-65, tgId=2) -/

/-- A single ML-DSA-65 ACVP key-generation test vector. -/
structure KeyGenVector where
  tcId : Nat
  seed : String
  pkFirst32 : String
  skFirst32 : String

/-- Embedded ML-DSA-65 ACVP key-generation vectors. -/
def keyGenVectors : Array KeyGenVector := #[
  { tcId := 26
    seed := "1BD67DC782B2958E189E315C040DD1F64C8AB232A6A170E1A7A52C33F10851B1"
    pkFirst32 := "43AD6560D3BB684667A559EE6EC7C816020E5B65671F270F2353A8C912B6C26B"
    skFirst32 := "43AD6560D3BB684667A559EE6EC7C816020E5B65671F270F2353A8C912B6C26B" },
  { tcId := 27
    seed := "B850D898A3D3D11C4E64ADE5A86FFED951B237C60D2A67A2DEF0A792B8F6990D"
    pkFirst32 := "712040468FC17996C93F18CEA90F4F58B7D8382C445211E1E81DC45B019CE2C8"
    skFirst32 := "712040468FC17996C93F18CEA90F4F58B7D8382C445211E1E81DC45B019CE2C8" },
  { tcId := 28
    seed := "455ECBD3C4A9EFB75A302DF08E770BF79E8605DC13ED57D7319AA6BFD1B6496B"
    pkFirst32 := "44882922421560C3655DD813D4A0D25CC453159C2F394A995C3F9BAF298F6BFF"
    skFirst32 := "44882922421560C3655DD813D4A0D25CC453159C2F394A995C3F9BAF298F6BFF" }
]

/-! ## Signature generation vectors (ML-DSA-65, deterministic)

Each vector specifies a 32-byte keygen seed and a message (both hex-encoded).
The test generates keys from the seed, signs the message with both Lean and
mldsa-native (with `rnd = 0^32`), and compares the results byte-exactly. -/

/-- A single ML-DSA-65 deterministic signature-generation test vector. -/
structure SigGenVector where
  tcId : Nat
  seed : String
  message : String

/-- Embedded ML-DSA-65 deterministic signature-generation vectors. -/
def sigGenVectors : Array SigGenVector := #[
  { tcId := 1
    seed := "1BD67DC782B2958E189E315C040DD1F64C8AB232A6A170E1A7A52C33F10851B1"
    message := "48656C6C6F" },
  { tcId := 2
    seed := "B850D898A3D3D11C4E64ADE5A86FFED951B237C60D2A67A2DEF0A792B8F6990D"
    message := "" },
  { tcId := 3
    seed := "455ECBD3C4A9EFB75A302DF08E770BF79E8605DC13ED57D7319AA6BFD1B6496B"
    message := "54657374" },
  { tcId := 4
    seed := "0000000000000000000000000000000000000000000000000000000000000000"
    message := "00" },
  { tcId := 5
    seed := "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    message := "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF" }
]

end MLDSA.Test.ACVP
