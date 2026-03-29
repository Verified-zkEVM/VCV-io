/*
 * Lean 4 FFI wrapper for SHA-3 / FIPS 202 primitives.
 *
 * Backed by the FIPS 202 implementation from mlkem-native.
 * Shared across ML-KEM (FIPS 203) and ML-DSA (FIPS 204).
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <lean/lean.h>
#include <string.h>

/* We only need the FIPS 202 headers from mlkem-native. */
#include "src/common.h"
#include "src/fips202/fips202.h"

static lean_obj_res lean_mk_byte_array_copy(const uint8_t *src, size_t n) {
  lean_object *arr = lean_alloc_sarray(1, n, n);
  memcpy(lean_sarray_cptr(arr), src, n);
  return arr;
}

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
