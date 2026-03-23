/*
 * Lean 4 FFI wrapper around mlkem-native (pq-code-package/mlkem-native).
 *
 * Exposes:
 *   - SHA-3 primitives (sha3_256, sha3_512, shake128, shake256)
 *   - End-to-end ML-KEM deterministic API (keypair_derand, enc_derand, dec)
 *
 * This file only includes headers for declarations; the implementations
 * come from mlkem_native.c compiled as a separate translation unit.
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <lean/lean.h>
#include <string.h>

/* ---------------------------------------------------------------------------
 * mlkem-native configuration (before any mlkem-native headers)
 * --------------------------------------------------------------------------- */

#ifndef MLK_CONFIG_NO_RANDOMIZED_API
#define MLK_CONFIG_NO_RANDOMIZED_API
#endif

#ifndef MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_PARAMETER_SET 768
#endif

/* Pull in declarations only (no implementations). */
#include "src/common.h"
#include "src/fips202/fips202.h"
#include "mlkem_native.h"

/* ---------------------------------------------------------------------------
 * Helper: allocate a Lean ByteArray of `n` bytes, copy `src` into it.
 * --------------------------------------------------------------------------- */
static lean_obj_res lean_mk_byte_array_copy(const uint8_t *src, size_t n) {
  lean_object *arr = lean_alloc_sarray(1, n, n);
  memcpy(lean_sarray_cptr(arr), src, n);
  return arr;
}

/* ---------------------------------------------------------------------------
 * Helper: allocate a Lean Prod (pair) of two objects.
 * --------------------------------------------------------------------------- */
static lean_obj_res lean_mk_pair(lean_obj_res a, lean_obj_res b) {
  lean_object *p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

/* ===========================================================================
 * SHA-3 / FIPS 202 wrappers
 * =========================================================================== */

LEAN_EXPORT lean_obj_res lean_sha3_256(b_lean_obj_arg input) {
  size_t inlen = lean_sarray_size(input);
  const uint8_t *in_ptr = lean_sarray_cptr(input);
  uint8_t out[32];
  mlk_sha3_256(out, in_ptr, inlen);
  return lean_mk_byte_array_copy(out, 32);
}

LEAN_EXPORT lean_obj_res lean_sha3_512(b_lean_obj_arg input) {
  size_t inlen = lean_sarray_size(input);
  const uint8_t *in_ptr = lean_sarray_cptr(input);
  uint8_t out[64];
  mlk_sha3_512(out, in_ptr, inlen);
  return lean_mk_byte_array_copy(out, 64);
}

LEAN_EXPORT lean_obj_res lean_shake256(b_lean_obj_arg input, size_t outlen) {
  size_t inlen = lean_sarray_size(input);
  const uint8_t *in_ptr = lean_sarray_cptr(input);
  lean_object *arr = lean_alloc_sarray(1, outlen, outlen);
  mlk_shake256(lean_sarray_cptr(arr), outlen, in_ptr, inlen);
  return arr;
}

LEAN_EXPORT lean_obj_res lean_shake128(b_lean_obj_arg input, size_t outlen) {
  size_t inlen = lean_sarray_size(input);
  const uint8_t *in_ptr = lean_sarray_cptr(input);

  lean_object *arr = lean_alloc_sarray(1, outlen, outlen);
  uint8_t *out_ptr = lean_sarray_cptr(arr);

  mlk_shake128ctx ctx;
  mlk_shake128_init(&ctx);
  mlk_shake128_absorb_once(&ctx, in_ptr, inlen);

  size_t pos = 0;
  while (pos + SHAKE128_RATE <= outlen) {
    mlk_shake128_squeezeblocks(out_ptr + pos, 1, &ctx);
    pos += SHAKE128_RATE;
  }
  if (pos < outlen) {
    uint8_t block[SHAKE128_RATE];
    mlk_shake128_squeezeblocks(block, 1, &ctx);
    memcpy(out_ptr + pos, block, outlen - pos);
  }

  mlk_shake128_release(&ctx);
  return arr;
}

/* ===========================================================================
 * End-to-end ML-KEM (deterministic API, fixed to MLK_CONFIG_PARAMETER_SET)
 * =========================================================================== */

LEAN_EXPORT lean_obj_res lean_mlkem_keypair_derand(b_lean_obj_arg coins) {
  const uint8_t *coins_ptr = lean_sarray_cptr(coins);
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  (void)crypto_kem_keypair_derand(pk, sk, coins_ptr);
  lean_obj_res pk_arr = lean_mk_byte_array_copy(pk, CRYPTO_PUBLICKEYBYTES);
  lean_obj_res sk_arr = lean_mk_byte_array_copy(sk, CRYPTO_SECRETKEYBYTES);
  return lean_mk_pair(pk_arr, sk_arr);
}

LEAN_EXPORT lean_obj_res lean_mlkem_enc_derand(b_lean_obj_arg ek,
                                               b_lean_obj_arg m) {
  const uint8_t *pk_ptr = lean_sarray_cptr(ek);
  const uint8_t *m_ptr = lean_sarray_cptr(m);
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t ss[CRYPTO_BYTES];
  (void)crypto_kem_enc_derand(ct, ss, pk_ptr, m_ptr);
  lean_obj_res ct_arr = lean_mk_byte_array_copy(ct, CRYPTO_CIPHERTEXTBYTES);
  lean_obj_res ss_arr = lean_mk_byte_array_copy(ss, CRYPTO_BYTES);
  return lean_mk_pair(ct_arr, ss_arr);
}

LEAN_EXPORT lean_obj_res lean_mlkem_dec(b_lean_obj_arg dk,
                                        b_lean_obj_arg ct) {
  const uint8_t *sk_ptr = lean_sarray_cptr(dk);
  const uint8_t *ct_ptr = lean_sarray_cptr(ct);
  uint8_t ss[CRYPTO_BYTES];
  (void)crypto_kem_dec(ss, ct_ptr, sk_ptr);
  return lean_mk_byte_array_copy(ss, CRYPTO_BYTES);
}
