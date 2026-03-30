/*
 * Generate Falcon test vectors from c-fn-dsa for the Lean test suite.
 * Compile: cc -std=c99 -O2 -I../../third_party/c-fn-dsa gen_testvectors.c ../../csrc/falcon/fndsa_native.c -o gen_testvectors
 * (run from csrc/falcon/)
 */

#include <stdio.h>
#include <string.h>
#include "../../third_party/c-fn-dsa/fndsa.h"

static void print_hex(const char *name, const uint8_t *data, size_t len, size_t max) {
    printf("    %s := \"", name);
    size_t show = (max > 0 && max < len) ? max : len;
    for (size_t i = 0; i < show; i++) {
        printf("%02X", data[i]);
    }
    printf("\"\n");
}

static void gen_vector(int idx, unsigned logn, const uint8_t *seed, size_t seed_len,
                       const uint8_t *msg, size_t msg_len,
                       const uint8_t *sign_seed, size_t sign_seed_len) {
    size_t sk_len = FNDSA_SIGN_KEY_SIZE(logn);
    size_t pk_len = FNDSA_VRFY_KEY_SIZE(logn);
    size_t sig_max = FNDSA_SIGNATURE_SIZE(logn);

    uint8_t sk[2560], pk[2048], sig[1536];
    fndsa_keygen_seeded(logn, seed, seed_len, sk, pk);

    size_t sig_len = fndsa_sign_seeded(
        sk, sk_len, NULL, 0,
        FNDSA_HASH_ID_RAW, msg, msg_len,
        sign_seed, sign_seed_len,
        sig, sig_max);

    int ver = fndsa_verify(
        sig, sig_len, pk, pk_len,
        NULL, 0, FNDSA_HASH_ID_RAW, msg, msg_len);

    printf("  { tcId := %d\n", idx);
    print_hex("seed", seed, seed_len, 0);
    print_hex("msg", msg, msg_len, 0);
    print_hex("signSeed", sign_seed, sign_seed_len, 0);
    printf("    skSize := %zu\n", sk_len);
    printf("    pkSize := %zu\n", pk_len);
    printf("    sigSize := %zu\n", sig_len);
    print_hex("pkFirst32", pk, pk_len, 32);
    print_hex("sigFirst32", sig, sig_len, 32);
    printf("    verifyResult := %s },\n", ver ? "true" : "false");
}

int main(void) {
    printf("-- Falcon-512 (logn=9) test vectors from c-fn-dsa\n\n");

    uint8_t seed1[48];
    for (int i = 0; i < 48; i++) seed1[i] = (uint8_t)i;
    uint8_t msg1[] = "Hello";
    uint8_t ss1[48];
    for (int i = 0; i < 48; i++) ss1[i] = (uint8_t)(0xFF - i);

    gen_vector(1, 9, seed1, 48, msg1, 5, ss1, 48);

    uint8_t seed2[48];
    for (int i = 0; i < 48; i++) seed2[i] = (uint8_t)(0xFF - i);
    uint8_t msg2[] = "Falcon test vector 2";
    uint8_t ss2[48];
    for (int i = 0; i < 48; i++) ss2[i] = (uint8_t)(i * 3 + 7);

    gen_vector(2, 9, seed2, 48, msg2, 20, ss2, 48);

    uint8_t seed3[48];
    for (int i = 0; i < 48; i++) seed3[i] = (uint8_t)(i * 7 + 13);
    uint8_t msg3[] = "";
    uint8_t ss3[48];
    for (int i = 0; i < 48; i++) ss3[i] = (uint8_t)(i * 5);

    gen_vector(3, 9, seed3, 48, msg3, 0, ss3, 48);

    return 0;
}
