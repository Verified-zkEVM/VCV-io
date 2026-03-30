/*
 * Generate FPR test vectors from c-fn-dsa for the Lean test suite.
 *
 * Compile (from csrc/falcon/):
 *   cc -std=c99 -O2 -DFNDSA_SSE2=0 -DFNDSA_NEON=0 -DFNDSA_RV64D=0 \
 *      -I../../third_party/c-fn-dsa gen_fpr_testvectors.c -o gen_fpr_testvectors
 *
 * The -D flags force the "plain" implementation path in sign_sampler.c,
 * which uses the integer-only FPR emulation matching our Lean code.
 */

#include <stdio.h>
#include <string.h>
#include <inttypes.h>

/* SCU: include all c-fn-dsa sources (same order as fndsa.c) */
#include "../../third_party/c-fn-dsa/util.c"
#include "../../third_party/c-fn-dsa/sha3.c"
#include "../../third_party/c-fn-dsa/sysrng.c"
#include "../../third_party/c-fn-dsa/codec.c"
#include "../../third_party/c-fn-dsa/kgen.c"
#include "../../third_party/c-fn-dsa/kgen_fxp.c"
#include "../../third_party/c-fn-dsa/kgen_gauss.c"
#include "../../third_party/c-fn-dsa/kgen_mp31.c"
#include "../../third_party/c-fn-dsa/kgen_ntru.c"
#include "../../third_party/c-fn-dsa/kgen_poly.c"
#include "../../third_party/c-fn-dsa/kgen_zint31.c"
#include "../../third_party/c-fn-dsa/mq.c"
#include "../../third_party/c-fn-dsa/sign_fpr.c"
#include "../../third_party/c-fn-dsa/sign_fpoly.c"
#include "../../third_party/c-fn-dsa/sign_sampler.c"
#include "../../third_party/c-fn-dsa/sign_core.c"
#include "../../third_party/c-fn-dsa/sign.c"
#include "../../third_party/c-fn-dsa/vrfy.c"

static void p(const char *name, fpr x) {
    printf("  -- %s\n", name);
    printf("  (0x%016" PRIX64 " : UInt64)\n", x);
}

static void pi(const char *name, int64_t x) {
    printf("  -- %s\n", name);
    printf("  %" PRId64 "\n", x);
}

static void pu(const char *name, uint64_t x) {
    printf("  -- %s\n", name);
    printf("  (0x%016" PRIX64 " : UInt64)\n", x);
}

int main(void) {
    fpr zero = FPR_ZERO;
    fpr one = fpr_of(1);
    fpr two = fpr_of(2);
    fpr half = fpr_div(one, two);

    printf("-- FPR test vectors from c-fn-dsa (plain/FPEMU path)\n\n");

    printf("-- Section: ofInt\n");
    p("ofInt 0", fpr_of(0));
    p("ofInt 1", fpr_of(1));
    p("ofInt 2", fpr_of(2));
    p("ofInt (-1)", fpr_of(-1));
    p("ofInt (-2)", fpr_of(-2));
    p("ofInt 42", fpr_of(42));
    p("ofInt (-42)", fpr_of(-42));
    p("ofInt 12289", fpr_of(12289));
    p("ofInt 100", fpr_of(100));
    p("ofInt 1000000", fpr_of(1000000));

    printf("\n-- Section: neg\n");
    p("neg(one)", fpr_neg(one));
    p("neg(neg(one))", fpr_neg(fpr_neg(one)));
    p("neg(two)", fpr_neg(two));
    p("neg(zero)", fpr_neg(zero));

    printf("\n-- Section: add\n");
    p("add(one, two)", fpr_add(one, two));
    p("add(one, neg(one))", fpr_add(one, fpr_neg(one)));
    p("add(one, one)", fpr_add(one, one));
    p("add(half, half)", fpr_add(half, half));
    fpr f42 = fpr_of(42);
    fpr f100 = fpr_of(100);
    p("add(42, 100)", fpr_add(f42, f100));

    printf("\n-- Section: sub\n");
    p("sub(two, one)", fpr_sub(two, one));
    p("sub(one, two)", fpr_sub(one, two));
    p("sub(one, one)", fpr_sub(one, one));
    p("sub(142, 42)", fpr_sub(fpr_of(142), f42));

    printf("\n-- Section: mul\n");
    p("mul(two, two)", fpr_mul(two, two));
    p("mul(one, one)", fpr_mul(one, one));
    p("mul(two, half)", fpr_mul(two, half));
    p("mul(42, 100)", fpr_mul(f42, f100));
    fpr q = fpr_of(12289);
    fpr invq = fpr_div(one, q);
    p("mul(q, 1/q)", fpr_mul(q, invq));

    printf("\n-- Section: div\n");
    p("div(one, two)", fpr_div(one, two));
    p("div(6, 3)", fpr_div(fpr_of(6), fpr_of(3)));
    p("div(100, 10)", fpr_div(f100, fpr_of(10)));
    p("div(one, q)", fpr_div(one, q));

    printf("\n-- Section: sqrt\n");
    p("sqrt(one)", fpr_sqrt(one));
    p("sqrt(4)", fpr_sqrt(fpr_of(4)));
    p("sqrt(two)", fpr_sqrt(two));
    p("sqrt(100)", fpr_sqrt(f100));

    printf("\n-- Section: rint\n");
    pi("rint(one)", fpr_rint(one));
    pi("rint(two)", fpr_rint(two));
    pi("rint(ofInt 42)", fpr_rint(f42));
    pi("rint(neg(ofInt 7))", fpr_rint(fpr_neg(fpr_of(7))));
    pi("rint(half)", fpr_rint(half));
    pi("rint(1.5)", fpr_rint(fpr_add(one, half)));
    pi("rint(2.5)", fpr_rint(fpr_add(two, half)));
    pi("rint(neg(half))", fpr_rint(fpr_neg(half)));

    printf("\n-- Section: floor\n");
    pi("floor(one)", fpr_floor(one));
    pi("floor(half)", fpr_floor(half));
    pi("floor(neg(half))", fpr_floor(fpr_neg(half)));
    pi("floor(1.5)", fpr_floor(fpr_add(one, half)));
    pi("floor(neg(1.5))", fpr_floor(fpr_neg(fpr_add(one, half))));
    pi("floor(ofInt 42)", fpr_floor(f42));

    printf("\n-- Section: scaled\n");
    p("scaled(1, 10)", fpr_scaled(1, 10));
    p("scaled(3, -1)", fpr_scaled(3, -1));
    p("scaled(5, 0)", fpr_scaled(5, 0));
    p("scaled(-7, 2)", fpr_scaled(-7, 2));

    printf("\n-- Section: expm_p63\n");
    pu("expm_p63(zero, one)", expm_p63(zero, one));
    pu("expm_p63(half, one)", expm_p63(half, one));
    pu("expm_p63(one, one)", expm_p63(one, one));
    pu("expm_p63(zero, half)", expm_p63(zero, half));
    pu("expm_p63(half, half)", expm_p63(half, half));
    fpr ln2 = FPR(6243314768165359, -53);
    pu("expm_p63(ln2, one)", expm_p63(ln2, one));
    fpr small = fpr_scaled(1, -10);
    pu("expm_p63(2^-10, one)", expm_p63(small, one));

    return 0;
}
