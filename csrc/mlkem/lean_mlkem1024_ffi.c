/*
 * Lean 4 FFI wrapper for ML-KEM-1024 (mlkem-native, parameter set 1024).
 * SPDX-License-Identifier: Apache-2.0
 */

#include <lean/lean.h>
#include <string.h>

#ifndef MLK_CONFIG_NO_RANDOMIZED_API
#define MLK_CONFIG_NO_RANDOMIZED_API
#endif

#ifndef MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_PARAMETER_SET 1024
#endif

#include "mlkem_native.h"

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

LEAN_EXPORT lean_obj_res lean_mlkem1024_keypair_derand(b_lean_obj_arg coins) {
  const uint8_t *coins_ptr = lean_sarray_cptr(coins);
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  (void)crypto_kem_keypair_derand(pk, sk, coins_ptr);
  lean_obj_res pk_arr = lean_mk_byte_array_copy(pk, CRYPTO_PUBLICKEYBYTES);
  lean_obj_res sk_arr = lean_mk_byte_array_copy(sk, CRYPTO_SECRETKEYBYTES);
  return lean_mk_pair(pk_arr, sk_arr);
}

LEAN_EXPORT lean_obj_res lean_mlkem1024_enc_derand(b_lean_obj_arg ek,
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

LEAN_EXPORT lean_obj_res lean_mlkem1024_dec(b_lean_obj_arg dk,
                                             b_lean_obj_arg ct) {
  const uint8_t *sk_ptr = lean_sarray_cptr(dk);
  const uint8_t *ct_ptr = lean_sarray_cptr(ct);
  uint8_t ss[CRYPTO_BYTES];
  (void)crypto_kem_dec(ss, ct_ptr, sk_ptr);
  return lean_mk_byte_array_copy(ss, CRYPTO_BYTES);
}
