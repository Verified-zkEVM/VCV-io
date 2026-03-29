/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCryptoTest.MLKEM.Helpers

/-!
# NIST ACVP Test Vectors for ML-KEM-768

Hardcoded test vectors from the NIST ACVP server
(https://github.com/usnistgov/ACVP-Server, ML-KEM-keyGen-FIPS203, tgId=2).

We store the full `d`, `z` inputs and the first 32 bytes of the expected `ek` and `dk` outputs
as fingerprints. The full byte-exact comparison against mlkem-native is done in the main test
suite; these vectors provide an independent cross-check against the official NIST expected values.
-/

set_option autoImplicit false

namespace MLKEM.Test.ACVP

structure KeyGenVector where
  tcId : Nat
  d : String
  z : String
  ekFirst32 : String
  dkFirst32 : String

def keyGenVectors : Array KeyGenVector := #[
  { tcId := 26
    d := "A2B4BCA315A6EA4600B4A316E09A2578AA1E8BCE919C8DF3A96C71C843F5B38B"
    z := "D6BF055CB7B375E3271ED131F1BA31F83FEF533A239878A71074578B891265D1"
    ekFirst32 := "5219C4CC17C35A828F3E21B2AB7496805C99EE041FCA0158A3314F07D053F364"
    dkFirst32 := "E6F634F0A3771ED789D6842321E147B6010ADA7B6B0B105949F90AEBECCA062C" },
  { tcId := 27
    d := "6DBB99AE6889AF01DA387D7D99BD4E91BACB11A6051B14AECD4C96F30CD9F9D9"
    z := "360557CADDFCF5FEE7C0DE6A363F095757588C35A3FD11C58677AB5E8797C2B8"
    ekFirst32 := "BC02284C2B36002A8E002311D6FA3ED17088D6157E76867ED2110B7E50A9F038"
    dkFirst32 := "54DB18751A289F68B462D90388629B33088C2AD32A834380B9E7AAE7DB510DC2" },
  { tcId := 28
    d := "7725321C56F925868FF834F5D1EE90A70332AA9283434E122C60A8D474AC6C0F"
    z := "00F6EEC72778E02ACD04BB056113C571982E45018BEAC566EC59953724F38A4B"
    ekFirst32 := "EAD840B81B03BFE75805595DCF0808B83738AF14C758920F80E209D68B9192C5"
    dkFirst32 := "C397104AE63A279795F3243F6EAC3A74AA0B414C822A668664826003F7CEDC26" }
]

end MLKEM.Test.ACVP
