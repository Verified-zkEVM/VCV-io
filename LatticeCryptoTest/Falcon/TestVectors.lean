/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Falcon-512 Test Vectors

Hardcoded test vectors generated from Thomas Pornin's c-fn-dsa reference
implementation using deterministic (`fndsa_keygen_seeded`, `fndsa_sign_seeded`)
APIs.

All vectors use `logn = 9` (Falcon-512) with raw message mode (no pre-hashing,
no domain-separation context).
-/


namespace Falcon.Test

structure KeyGenVector where
  tcId : Nat
  seed : String
  pkSize : Nat
  skSize : Nat
  pkFirst32 : String

structure SignVerifyVector where
  tcId : Nat
  seed : String
  msg : String
  signSeed : String
  skSize : Nat
  pkSize : Nat
  sigSize : Nat
  pkFirst32 : String
  sigFirst32 : String
  verifyResult : Bool

def signVerifyVectors : Array SignVerifyVector := #[
  { tcId := 1
    seed := "000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F\
202122232425262728292A2B2C2D2E2F"
    msg := "48656C6C6F"
    signSeed := "FFFEFDFCFBFAF9F8F7F6F5F4F3F2F1F0EFEEEDECEBEAE9E8E7E6E5E4E3E2\
E1E0DFDEDDDCDBDAD9D8D7D6D5D4D3D2D1D0"
    skSize := 1281
    pkSize := 897
    sigSize := 666
    pkFirst32 := "090A35A1F352EED2AFCCA956E385BCA34AFD069D4EC7B1CD6101F895FF154D2B"
    sigFirst32 := "39382BC51B07D5C644D3155249628A7304A40DE5D6CE7E199600583FD65F7891"
    verifyResult := true },
  { tcId := 2
    seed := "FFFEFDFCFBFAF9F8F7F6F5F4F3F2F1F0EFEEEDECEBEAE9E8E7E6E5E4E3E2\
E1E0DFDEDDDCDBDAD9D8D7D6D5D4D3D2D1D0"
    msg := "46616C636F6E207465737420766563746F722032"
    signSeed := "070A0D101316191C1F2225282B2E3134373A3D404346494C4F5255585B5E\
6164676A6D707376797C7F8285888B8E9194"
    skSize := 1281
    pkSize := 897
    sigSize := 666
    pkFirst32 := "09578A7AD7A3DA1F77D5F6E67B283F3C2D0296A661CF24CE2EF0D95E78A80EF0"
    sigFirst32 := "39149CD06FB640FF5428B3BEC19D00EC5E1E9B1CFF02B3E5216860759E182F2C"
    verifyResult := true },
  { tcId := 3
    seed := "0D141B222930373E454C535A61686F767D848B9299A0A7AEB5BCC3CAD1D8DF\
E6EDF4FB020910171E252C333A41484F56"
    msg := ""
    signSeed := "00050A0F14191E23282D32373C41464B50555A5F64696E73787D82878C91\
969BA0A5AAAFB4B9BEC3C8CDD2D7DCE1E6EB"
    skSize := 1281
    pkSize := 897
    sigSize := 666
    pkFirst32 := "094C3E191A5FDE79641CB8FA720B66A3A521EA4D8BB7A7660B71268D03B73EA4"
    sigFirst32 := "39FE32CFD16E92CA09C173F631717DB39AD522DAF0B5D2B5FDD7BB40E108CC3A"
    verifyResult := true }
]

end Falcon.Test
