# Primitive-vector provenance and notice

The numeric SHA-2, HMAC, and SHAKE example values projected in this directory come from the
National Institute of Standards and Technology (NIST) sources identified byte-for-byte in
`vectors.json`. NIST technical-series publications are U.S. Government works. NIST material is
credited here as the source; its appearance does not imply NIST endorsement of this project or a
validation certificate. The source archives and examples are provided without warranty, and these
projections are regression/conformance evidence only.

The 272-byte empty-message SHAKE256 value is the exact leading-byte projection of NIST's 4096-bit
`SHAKE256_Msg0.pdf` output. The 32-byte outputs for 135, 136, and 137 repetitions of byte `0x61`
are independently derived rate-boundary regressions, not NIST vectors. `vectors.json` records the
exact Python `hashlib.shake_256` derivation and independent OpenSSL corroboration.

The SHA-224, SHA-384, SHA-512/224, SHA-512/256, SHA-3, and SHAKE128 examples are independently
derived regressions. They cover `abc`, SHA-2 padding neighbors, SHA-3 exact-rate padding, and a
multi-block SHAKE128 squeeze. `vectors.json` records the exact messages and independent
Python/OpenSSL derivation boundary; these cases are not described as official NIST vectors.

MGF1 has no standalone official vector corpus in RFC 8017. Its two compact cases are derived from
the RFC's four-byte big-endian counter grammar and are explicitly classified as regression-only.
RFC 8017 is Copyright (c) 2016 IETF Trust and the persons identified as its authors, subject to the
IETF Trust's Legal Provisions Relating to IETF Documents. No RFC text or code component is copied
into this projection.

The all-profile fingerprints are independently generated test evidence for the exact FIPS 205
Section 11 concatenation grammars. They are not NIST vectors and not an implementation-validation
claim.
