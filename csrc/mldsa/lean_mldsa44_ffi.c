/*
 * Lean 4 FFI wrapper for ML-DSA-44 (mldsa-native, parameter set 44).
 * SPDX-License-Identifier: Apache-2.0
 */

#include <lean/lean.h>
#include <string.h>

#ifndef MLD_CONFIG_PARAMETER_SET
#define MLD_CONFIG_PARAMETER_SET 44
#endif

#include "mldsa_native.h"

#define MLDSA44_PK_BYTES MLDSA_PUBLICKEYBYTES(44)
#define MLDSA44_SK_BYTES MLDSA_SECRETKEYBYTES(44)
#define MLDSA44_SIG_BYTES MLDSA_BYTES(44)
#define MLDSA_SEED_BYTES 32
#define MLDSA_RND_BYTES 32

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

LEAN_EXPORT lean_obj_res lean_mldsa44_keypair_internal(b_lean_obj_arg seed) {
  if (lean_sarray_size(seed) != MLDSA_SEED_BYTES) {
    return lean_mk_pair(lean_mk_byte_array_copy((const uint8_t *)"", 0),
                        lean_mk_byte_array_copy((const uint8_t *)"", 0));
  }
  const uint8_t *seed_ptr = lean_sarray_cptr(seed);
  uint8_t pk[MLDSA44_PK_BYTES];
  uint8_t sk[MLDSA44_SK_BYTES];
  (void)MLD_API_NAMESPACE(keypair_internal)(pk, sk, seed_ptr);
  lean_obj_res pk_arr = lean_mk_byte_array_copy(pk, MLDSA44_PK_BYTES);
  lean_obj_res sk_arr = lean_mk_byte_array_copy(sk, MLDSA44_SK_BYTES);
  return lean_mk_pair(pk_arr, sk_arr);
}

LEAN_EXPORT lean_obj_res lean_mldsa44_sign_internal(b_lean_obj_arg sk,
                                                     b_lean_obj_arg msg,
                                                     b_lean_obj_arg rnd) {
  if (lean_sarray_size(sk) != MLDSA44_SK_BYTES ||
      lean_sarray_size(rnd) != MLDSA_RND_BYTES) {
    return lean_mk_byte_array_copy((const uint8_t *)"", 0);
  }
  const uint8_t *sk_ptr = lean_sarray_cptr(sk);
  const uint8_t *msg_ptr = lean_sarray_cptr(msg);
  size_t msg_len = lean_sarray_size(msg);
  const uint8_t *rnd_ptr = lean_sarray_cptr(rnd);

  uint8_t sig[MLDSA44_SIG_BYTES];
  size_t siglen = 0;

  int rc = MLD_API_NAMESPACE(signature_internal)(
      sig, &siglen, msg_ptr, msg_len, NULL, 0, rnd_ptr, sk_ptr, 0);
  if (rc != 0 || siglen == 0) {
    return lean_mk_byte_array_copy((const uint8_t *)"", 0);
  }
  return lean_mk_byte_array_copy(sig, siglen);
}

LEAN_EXPORT uint8_t lean_mldsa44_verify_internal(b_lean_obj_arg pk,
                                                  b_lean_obj_arg msg,
                                                  b_lean_obj_arg sig) {
  if (lean_sarray_size(pk) != MLDSA44_PK_BYTES ||
      lean_sarray_size(sig) != MLDSA44_SIG_BYTES) {
    return 0;
  }
  const uint8_t *pk_ptr = lean_sarray_cptr(pk);
  const uint8_t *msg_ptr = lean_sarray_cptr(msg);
  size_t msg_len = lean_sarray_size(msg);
  const uint8_t *sig_ptr = lean_sarray_cptr(sig);
  size_t sig_len = lean_sarray_size(sig);

  int rc = MLD_API_NAMESPACE(verify_internal)(
      sig_ptr, sig_len, msg_ptr, msg_len, NULL, 0, pk_ptr, 0);
  return (rc == 0) ? 1 : 0;
}
