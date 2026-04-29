/*
 * Single Compilation Unit (SCU) amalgamation of c-fn-dsa.
 *
 * This file #include's every c-fn-dsa translation unit so that the
 * entire library compiles as a single object, matching the
 * mlkem-native / mldsa-native pattern used elsewhere in this project.
 *
 * Include order matters: kgen*.c files must come before mq.c because
 * mq.c defines macros (R, R2) that collide with kgen_inner.h
 * parameter names.
 *
 * SPDX-License-Identifier: Unlicense
 */

/* Utilities and system RNG (no conflicting macros) */
#include "../../third_party/c-fn-dsa/util.c"
#include "../../third_party/c-fn-dsa/sha3.c"
#include "../../third_party/c-fn-dsa/sysrng.c"
#include "../../third_party/c-fn-dsa/codec.c"

/* Key generation (uses R2 as parameter name in kgen_inner.h) */
#include "../../third_party/c-fn-dsa/kgen.c"
#include "../../third_party/c-fn-dsa/kgen_fxp.c"
#include "../../third_party/c-fn-dsa/kgen_gauss.c"
#include "../../third_party/c-fn-dsa/kgen_mp31.c"
#include "../../third_party/c-fn-dsa/kgen_ntru.c"
#include "../../third_party/c-fn-dsa/kgen_poly.c"
#include "../../third_party/c-fn-dsa/kgen_zint31.c"

/* Modular arithmetic (defines R, R2 macros -- must come after kgen) */
#include "../../third_party/c-fn-dsa/mq.c"

/* Signing */
#include "../../third_party/c-fn-dsa/sign_fpr.c"
#include "../../third_party/c-fn-dsa/sign_fpoly.c"
#include "../../third_party/c-fn-dsa/sign_sampler.c"
#include "../../third_party/c-fn-dsa/sign_core.c"
#include "../../third_party/c-fn-dsa/sign.c"

/* Verification */
#include "../../third_party/c-fn-dsa/vrfy.c"
