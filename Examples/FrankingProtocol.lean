/-
Copyright (c) 2025 Gabe Robison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabe Robison
-/

import VCVio

/-!
# Message Franking Protocol

This file implements a message franking protocol for secure abuse reporting in encrypted
messaging systems, allowing recipients to verifiably report abusive messages while
maintaining encryption of legitimate messages.
-/

-- nonce generation using OracleComp
def generate_nonce : OracleComp unifSpec (BitVec 256) :=
  $ᵗ BitVec 256

-- helpers for converting String's & BitVec's
def string_to_bitvec (s : String) : BitVec 256 :=
  s.foldl (λ acc c => (acc.shiftLeft 8) + BitVec.ofNat 256 c.toNat) 0

def bitvec_to_string (bv : BitVec 256) : String :=
  let rec chars (n : Nat) (acc : List Char) :=
    if n = 0 then acc
    else chars (n / 256) (Char.ofNat (n % 256) :: acc)
  String.mk (chars bv.toNat [])

-- mock HMAC-SHA256
def mock_hmac_sha256_out_type : Type := String
instance : Repr mock_hmac_sha256_out_type := instReprString

def mock_hmac_sha256 (key : BitVec 256) (data : BitVec 256) : mock_hmac_sha256_out_type :=
  "HMAC_SHA256_OUT(" ++ bitvec_to_string key  ++ "," ++ bitvec_to_string data ++ ")"

-- mock encryption/decryption
def mock_encrypt (msg : BitVec 256) : BitVec 256 :=
  msg ^^^ (BitVec.ofNat 256 0xABCDEF)

def mock_decrypt (ciphertext : BitVec 256) : BitVec 256 :=
  ciphertext ^^^ (BitVec.ofNat 256 0xABCDEF)

-- structures
structure SecretMessage where
  content : String
  nonce : BitVec 256
  deriving Repr

structure EncryptedMessage where
  ciphertext : BitVec 256
  deriving Repr

structure Context where
  sender_id : BitVec 256
  recipient_id : BitVec 256
  timestamp : Nat
  message_id : Nat
  deriving Repr

structure FrankingTag where
  tag : mock_hmac_sha256_out_type --mock_hmac_sha256_out_type
  deriving Repr

structure ReportingTag where
  tag : mock_hmac_sha256_out_type --mock_hmac_sha256_out_type
  deriving Repr

structure MessagePackage where
  encrypted_message : EncryptedMessage
  franking_tag : FrankingTag
  reporting_tag : ReportingTag
  context : Context
  nonce : BitVec 256
  deriving Repr

structure AbuseReport where
  message : SecretMessage
  franking_tag : FrankingTag
  reporting_tag : ReportingTag
  context : Context
  deriving Repr

-- dealing with serialization
-- navigating append (++) proving tedious, using a tuple for now instead of xor
def serialize_message_data (msg : String) (nonce : BitVec 256) : BitVec 256 × BitVec 256 :=
  let msg_bv := string_to_bitvec msg
  (msg_bv, nonce)

def deserialize_message_data (data : BitVec 256 × BitVec 256) : String × BitVec 256 :=
  let (msg_bv, nonce) := data
  (bitvec_to_string msg_bv, nonce)

-- generating tags
def generate_franking_tag (nonce : BitVec 256) (msg : String) : FrankingTag :=
  let (msg_bv, _) := serialize_message_data msg nonce
  let tf := mock_hmac_sha256 nonce msg_bv -- TF = HMAC·SHA256(NF, M)
  { tag := tf }

def generate_reporting_tag (franking_tag : FrankingTag) (context : Context)
    (facebook_key : BitVec 256) : ReportingTag :=
  -- RF = HMAC·SHA256(KF, TF||context)
  let context_bv := BitVec.ofNat 256 context.timestamp
  let serialized := franking_tag.tag.append (bitvec_to_string context_bv)
  let rf_tag := mock_hmac_sha256 facebook_key (string_to_bitvec serialized)
  { tag := rf_tag }

-- message encryption/decryption
def prepare_encrypted_message (content : String) (nonce : BitVec 256) : EncryptedMessage :=
  let (msg_bv, _) := serialize_message_data content nonce
  { ciphertext := mock_encrypt msg_bv }

def decrypt_message (encrypted_msg : EncryptedMessage) (nonce : BitVec 256) : String :=
  let decrypted_bv := mock_decrypt encrypted_msg.ciphertext
  let (msg, _) := deserialize_message_data (decrypted_bv, nonce)
  msg


-- instance for mock_sha256 comparison (decidable equality)
instance : DecidableEq mock_hmac_sha256_out_type :=
  fun x y => match String.decEq x y with
  | isTrue h => isTrue h
  | isFalse h => isFalse h

-- verify the message by recomputing the franking tag.
-- struggling w/ guard operation
def verify_message_package
    (package : MessagePackage) : OracleComp unifSpec (Option SecretMessage) := do
  let content := decrypt_message package.encrypted_message package.nonce
  let (msg_bv, _) := serialize_message_data content package.nonce
  let computed_tf := mock_hmac_sha256 package.nonce msg_bv
  if computed_tf = package.franking_tag.tag then
    return some { content := content, nonce := package.nonce }
  else
    return none

-- -- DEVON: made this an `OracleComp` so you can fail explicitly with guard
-- def verify_message_package (package : MessagePackage) : OracleComp unifSpec SecretMessage := do
--   let content := decrypt_message package.encrypted_message package.nonce
--   let serialized_data := package.nonce.xor (string_to_bitvec content)
--   let computed_tf := mock_hmac_sha256 package.nonce serialized_data
--   -- `guard` statement will fail if the franking tag is wrong
--   guard (computed_tf = package.franking_tag.tag)
--   return { content := content, nonce := package.nonce }

-- report validation by fb
def validate_abuse_report (report : AbuseReport) (facebook_key : BitVec 256) : Bool :=
  let (msg_bv, _) := serialize_message_data report.message.content report.message.nonce
  let computed_tf := mock_hmac_sha256 report.message.nonce msg_bv
  let context_bv := BitVec.ofNat 256 report.context.timestamp
  let serialized := report.franking_tag.tag.append (bitvec_to_string context_bv)
  let computed_rf := mock_hmac_sha256 facebook_key (string_to_bitvec serialized)
  (computed_tf = report.franking_tag.tag) && (computed_rf = report.reporting_tag.tag)

structure SimulationData where
  verified_msg : SecretMessage
  message_package : MessagePackage
  facebook_key : BitVec 256
  deriving Repr

def simulation_setup (message_content : String) : OracleComp unifSpec (Option SimulationData) := do
  let facebook_key := BitVec.ofNat 256 123456789
  let context : Context := {
    sender_id := BitVec.ofNat 256 1001, recipient_id := BitVec.ofNat 256 1002,
    timestamp := 1730230302,
    message_id := 123 }
  let nonce ← generate_nonce
  let franking_tag  := generate_franking_tag nonce message_content
  let encrypted_msg := prepare_encrypted_message message_content nonce
  let reporting_tag := generate_reporting_tag franking_tag context facebook_key
  let package : MessagePackage := {
    encrypted_message := encrypted_msg,
    franking_tag := franking_tag,
    reporting_tag := reporting_tag,
    context := context,
    nonce := nonce }
  let maybeVerifiedMsg ← verify_message_package package
  match maybeVerifiedMsg with
  | none => -- verification fail
    return none
  | some verified_msg =>
    return some { verified_msg := verified_msg
                  message_package := package
                  facebook_key := facebook_key }

def test_abuse_report_validation : IO Unit := do
  let message_content := "Hello world"
  let manipulated_message := "Hell world"
  let maybeData ← OracleComp.runIO (simulation_setup message_content)
  match maybeData with
  | none =>
    IO.println "setup failed"
  | some data =>
    let valid_abuse_report := {
      message := data.verified_msg,
      franking_tag := data.message_package.franking_tag,
      reporting_tag := data.message_package.reporting_tag,
      context := data.message_package.context }
    let is_valid := validate_abuse_report valid_abuse_report data.facebook_key
    IO.println s!"valid abuse report validation result: {is_valid}"

    let invalid_abuse_report := {
      message := {
        content := manipulated_message,
        nonce := data.verified_msg.nonce },
      franking_tag := data.message_package.franking_tag,
      reporting_tag := data.message_package.reporting_tag,
      context := data.message_package.context }
    let is_invalid := validate_abuse_report invalid_abuse_report data.facebook_key
    IO.println s!"false abuse report validation result: {is_invalid}"

-- Theorems and lemmas
@[simp]
lemma BitVec.xor_xor_cancel_right {n : ℕ} (bv1 bv2 : BitVec n) :
    bv1 ^^^ bv2 ^^^ bv2 = bv1 :=
  by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

@[simp]
lemma bitvec_to_string_to_bitvec (bv : BitVec 256) :
    string_to_bitvec (bitvec_to_string bv) = bv := by
  simp [string_to_bitvec, bitvec_to_string]
  sorry

@[simp]
lemma mock_decrypt_mock_encrypt (msg : BitVec 256) :
    mock_decrypt (mock_encrypt msg) = msg := by
  simp [mock_decrypt, mock_encrypt]

-- looking to prove that: "turning in a valid reporting tag always works"

theorem validateAbuseReport_is_sound (message_content : String) :
    [= true | do
      -- basically simulation_setup
      let facebook_key := BitVec.ofNat 256 123456789
      let context : Context := {
        sender_id := BitVec.ofNat 256 1001,
        recipient_id := BitVec.ofNat 256 1002,
        timestamp := 1730230302,
        message_id := 123 }
      -- simulation data
      let maybeData ← simulation_setup message_content
      match maybeData with
      | none => return false
      | some data =>
        let valid_abuse_report := {
          message := data.verified_msg,
          franking_tag := data.message_package.franking_tag,
          reporting_tag := data.message_package.reporting_tag,
          context := data.message_package.context }
        -- validation result
        return validate_abuse_report valid_abuse_report data.facebook_key] = 1 := by
  simp [simulation_setup, validate_abuse_report, verify_message_package,
        generate_franking_tag, prepare_encrypted_message,
        generate_reporting_tag, decrypt_message, generate_nonce]
  simp [Finset.ext_iff]
  sorry

-- valid messages always pass verification
lemma simulation_setup_succeeds (message_content : String) :
    [⊥ | do
      let maybeData ← simulation_setup message_content
      match maybeData with
      | none => return true
      | some _ => return false] = 0 := by
  simp [simulation_setup, verify_message_package,
        generate_franking_tag, prepare_encrypted_message,
        generate_reporting_tag, decrypt_message, generate_nonce]
  sorry

-- will never fail to validate the message if it is generated safely
lemma probFailure_verify_message_valid_message (facebook_key : BitVec 256)
    (message_content : String) (context : Context) :
    [⊥ | do
      let nonce ← generate_nonce
      let franking_tag := generate_franking_tag nonce message_content
      let encrypted_msg := prepare_encrypted_message message_content nonce
      let reporting_tag := generate_reporting_tag franking_tag context facebook_key
      let package := {
        encrypted_message := encrypted_msg,
        franking_tag := franking_tag,
        reporting_tag := reporting_tag,
        context := context,
        nonce := nonce
      }
      verify_message_package package] = 0 := by
  simp [generate_franking_tag, prepare_encrypted_message,
    verify_message_package, decrypt_message, generate_nonce]
  sorry
