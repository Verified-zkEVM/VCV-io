/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Test.Helpers

/-!
# NIST ACVP Test Vectors for ML-DSA-65

Hardcoded test vectors from the NIST ACVP server
(https://github.com/usnistgov/ACVP-Server, ML-DSA-keyGen/sigGen/sigVer-FIPS204).

For keygen: we store the full 32-byte seed and the first 32 bytes of the expected pk and sk
outputs as fingerprints. The full byte-exact comparison against mldsa-native is done in the
end-to-end tests; these vectors provide an independent cross-check against the official NIST
expected values.

For siggen: deterministic vectors (tgId=3), we store the first 32 bytes of sk, the full message,
and the first 32 bytes of the expected signature.

For sigver: we store the first 32 bytes of pk, the first 32 bytes of the message, the first 32
bytes of the signature, and the expected pass/fail result.
-/

set_option autoImplicit false

namespace MLDSA.Test.ACVP

/-! ## Key generation vectors (ML-DSA-65, tgId=2) -/

structure KeyGenVector where
  tcId : Nat
  seed : String
  pkFirst32 : String
  skFirst32 : String

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

/-! ## Signature generation vectors (ML-DSA-65, deterministic, tgId=3) -/

structure SigGenVector where
  tcId : Nat
  skFirst32 : String
  message : String
  sigFirst32 : String

def sigGenVectors : Array SigGenVector := #[
  { tcId := 31
    skFirst32 := "6CD5B575E6B85BFAD904C66BFDFDCA515265C07FB8CAAAC9C58C14FA9189D491"
    message := "A54CB4BF79DDCE7D7C446F972A849DC3C75917E7ED52\
777590D49BA28A8171B107650CC74348C2FD5AA5327FED13BBDF514ECCD477F4\
D5B213F8083CDB2923AFC35DABE663EE12932E8FDCC3058B6D991176CBAD"
    sigFirst32 := "E47D117DF51F7B54875CEA55017BE42F1DB20373EFC790331516CFFC243D8C18" },
  { tcId := 32
    skFirst32 := "757B9B91D95449B3478F9E05715EE8BBDDB5AACCF25DC4CA6CC2616826AD4B02"
    message := "C9210DD41B6FE28B2AA9459F1011844E975383D558C64D\
21402FA47B55E3B9BB7F5091A8C323923B434240F6C2813EACCE6B3984B6530A\
5ACAD1F8ADAA25CD6BA1903F9C18F06F87398CB3FFA8D13F64A9FDD"
    sigFirst32 := "B153B253B8443D05E9CC198DFD847D9AC2D227E1860FBAE37F7E52926175AAE5" }
]

/-! ## Signature verification vectors (ML-DSA-65, tgId=4) -/

structure SigVerVector where
  tcId : Nat
  testPassed : Bool
  pkFirst32 : String
  msgFirst32 : String
  sigFirst32 : String
  reason : String

def sigVerVectors : Array SigVerVector := #[
  { tcId := 31
    testPassed := true
    pkFirst32 := "156EAF9AA279E22DE502D44C382A2A3F92A437F86DB4935310D8D65FFABB6240"
    msgFirst32 := "FF8B46A280AF686BE484DFE0F38A852760DAB909111BCB1BE8A6C83DEF1CFF58"
    sigFirst32 := "1F1A3CCE562CA78C6C194AD3D7301177D7BE919C4B692B87EC3C0359E03E0C83"
    reason := "valid signature and message" },
  { tcId := 32
    testPassed := false
    pkFirst32 := "95DBAC429AD329918E910A5206B197D58A955A7E8041E1F8E330ABEF102A0815"
    msgFirst32 := "B98CA6127F0B561F4E7DBAB60BC1BD92E562F39A51B98FA9CB97563B9942AC40"
    sigFirst32 := "4FED2DCA3CA23994BC1AEF5F4D964555CA74B85ACF53E822DC2FE1B6A99EEC1A"
    reason := "modified signature - hint" },
  { tcId := 33
    testPassed := false
    pkFirst32 := "8C902EFF5B30E8E28F5D71A970534256578A419D50E9B2864E574BC684DA4F23"
    msgFirst32 := "1A4B63BC02B51640D9DF87EE12148C08A562C08649D56ABD759A5104DB069CDB"
    sigFirst32 := "644491FA237B8EE1008368895591B5226B4C84F10E50EC787BBEA92832D4F8BB"
    reason := "modified message" }
]

end MLDSA.Test.ACVP
