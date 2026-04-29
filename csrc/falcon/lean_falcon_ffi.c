/*
 * Lean 4 FFI wrapper around c-fn-dsa (pornin/c-fn-dsa).
 *
 * Exposes FN-DSA (Falcon) APIs for both Falcon-512 (logn=9) and
 * Falcon-1024 (logn=10):
 *   - keygen_seeded
 *   - sign_seeded  (deterministic, raw message)
 *   - verify       (raw message)
 *
 * SPDX-License-Identifier: Unlicense
 */

#include <lean/lean.h>
#include <string.h>
#include "../../third_party/c-fn-dsa/fndsa.h"

/* Falcon-512 sizes (logn = 9) */
#define F512_SK_BYTES  FNDSA_SIGN_KEY_SIZE(9)
#define F512_PK_BYTES  FNDSA_VRFY_KEY_SIZE(9)
#define F512_SIG_BYTES FNDSA_SIGNATURE_SIZE(9)

/* Falcon-1024 sizes (logn = 10) */
#define F1024_SK_BYTES  FNDSA_SIGN_KEY_SIZE(10)
#define F1024_PK_BYTES  FNDSA_VRFY_KEY_SIZE(10)
#define F1024_SIG_BYTES FNDSA_SIGNATURE_SIZE(10)

static lean_obj_res lean_mk_byte_array_copy(const uint8_t *src, size_t n) {
    lean_object *arr = lean_alloc_sarray(1, n, n);
    memcpy(lean_sarray_cptr(arr), src, n);
    return arr;
}

static lean_obj_res lean_mk_pair(lean_obj_res a, lean_obj_res b) {
    lean_object *p = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p, 0, a);
    lean_ctor_set(p, 1, b);
    return p;
}

/* ── Falcon-512 ─────────────────────────────────────────────────── */

/*
 * lean_falcon512_keygen_seeded(seed : ByteArray) : ByteArray × ByteArray
 *
 * Deterministic keygen from seed. Returns (sk, pk).
 */
LEAN_EXPORT lean_obj_res lean_falcon512_keygen_seeded(b_lean_obj_arg seed) {
    const uint8_t *seed_ptr = lean_sarray_cptr(seed);
    size_t seed_len = lean_sarray_size(seed);
    uint8_t sk[F512_SK_BYTES];
    uint8_t pk[F512_PK_BYTES];
    fndsa_keygen_seeded(9, seed_ptr, seed_len, sk, pk);
    lean_obj_res sk_arr = lean_mk_byte_array_copy(sk, F512_SK_BYTES);
    lean_obj_res pk_arr = lean_mk_byte_array_copy(pk, F512_PK_BYTES);
    return lean_mk_pair(sk_arr, pk_arr);
}

/*
 * lean_falcon512_sign_seeded(sk : ByteArray, msg : ByteArray,
 *                            seed : ByteArray) : ByteArray
 *
 * Deterministic signing (raw message, no context / pre-hash).
 * Returns signature bytes, or empty ByteArray on failure.
 */
LEAN_EXPORT lean_obj_res lean_falcon512_sign_seeded(b_lean_obj_arg sk,
                                                     b_lean_obj_arg msg,
                                                     b_lean_obj_arg seed) {
    const uint8_t *sk_ptr = lean_sarray_cptr(sk);
    size_t sk_len = lean_sarray_size(sk);
    const uint8_t *msg_ptr = lean_sarray_cptr(msg);
    size_t msg_len = lean_sarray_size(msg);
    const uint8_t *seed_ptr = lean_sarray_cptr(seed);
    size_t seed_len = lean_sarray_size(seed);

    uint8_t sig[F512_SIG_BYTES];
    size_t sig_len = fndsa_sign_seeded(
        sk_ptr, sk_len,
        NULL, 0,
        FNDSA_HASH_ID_RAW, msg_ptr, msg_len,
        seed_ptr, seed_len,
        sig, sizeof(sig));
    if (sig_len == 0) {
        return lean_mk_byte_array_copy((const uint8_t *)"", 0);
    }
    return lean_mk_byte_array_copy(sig, sig_len);
}

/*
 * lean_falcon512_verify(pk : ByteArray, msg : ByteArray,
 *                       sig : ByteArray) : UInt8
 *
 * Verify a signature (raw message, no context / pre-hash).
 * Returns 1 on success, 0 on failure.
 */
LEAN_EXPORT uint8_t lean_falcon512_verify(b_lean_obj_arg pk,
                                           b_lean_obj_arg msg,
                                           b_lean_obj_arg sig) {
    const uint8_t *sig_ptr = lean_sarray_cptr(sig);
    size_t sig_len = lean_sarray_size(sig);
    const uint8_t *pk_ptr = lean_sarray_cptr(pk);
    size_t pk_len = lean_sarray_size(pk);
    const uint8_t *msg_ptr = lean_sarray_cptr(msg);
    size_t msg_len = lean_sarray_size(msg);

    int rc = fndsa_verify(
        sig_ptr, sig_len,
        pk_ptr, pk_len,
        NULL, 0,
        FNDSA_HASH_ID_RAW, msg_ptr, msg_len);
    return (rc == 1) ? 1 : 0;
}

/* ── Falcon-1024 ────────────────────────────────────────────────── */

LEAN_EXPORT lean_obj_res lean_falcon1024_keygen_seeded(b_lean_obj_arg seed) {
    const uint8_t *seed_ptr = lean_sarray_cptr(seed);
    size_t seed_len = lean_sarray_size(seed);
    uint8_t sk[F1024_SK_BYTES];
    uint8_t pk[F1024_PK_BYTES];
    fndsa_keygen_seeded(10, seed_ptr, seed_len, sk, pk);
    lean_obj_res sk_arr = lean_mk_byte_array_copy(sk, F1024_SK_BYTES);
    lean_obj_res pk_arr = lean_mk_byte_array_copy(pk, F1024_PK_BYTES);
    return lean_mk_pair(sk_arr, pk_arr);
}

LEAN_EXPORT lean_obj_res lean_falcon1024_sign_seeded(b_lean_obj_arg sk,
                                                      b_lean_obj_arg msg,
                                                      b_lean_obj_arg seed) {
    const uint8_t *sk_ptr = lean_sarray_cptr(sk);
    size_t sk_len = lean_sarray_size(sk);
    const uint8_t *msg_ptr = lean_sarray_cptr(msg);
    size_t msg_len = lean_sarray_size(msg);
    const uint8_t *seed_ptr = lean_sarray_cptr(seed);
    size_t seed_len = lean_sarray_size(seed);

    uint8_t sig[F1024_SIG_BYTES];
    size_t sig_len = fndsa_sign_seeded(
        sk_ptr, sk_len,
        NULL, 0,
        FNDSA_HASH_ID_RAW, msg_ptr, msg_len,
        seed_ptr, seed_len,
        sig, sizeof(sig));
    if (sig_len == 0) {
        return lean_mk_byte_array_copy((const uint8_t *)"", 0);
    }
    return lean_mk_byte_array_copy(sig, sig_len);
}

LEAN_EXPORT uint8_t lean_falcon1024_verify(b_lean_obj_arg pk,
                                            b_lean_obj_arg msg,
                                            b_lean_obj_arg sig) {
    const uint8_t *sig_ptr = lean_sarray_cptr(sig);
    size_t sig_len = lean_sarray_size(sig);
    const uint8_t *pk_ptr = lean_sarray_cptr(pk);
    size_t pk_len = lean_sarray_size(pk);
    const uint8_t *msg_ptr = lean_sarray_cptr(msg);
    size_t msg_len = lean_sarray_size(msg);

    int rc = fndsa_verify(
        sig_ptr, sig_len,
        pk_ptr, pk_len,
        NULL, 0,
        FNDSA_HASH_ID_RAW, msg_ptr, msg_len);
    return (rc == 1) ? 1 : 0;
}
