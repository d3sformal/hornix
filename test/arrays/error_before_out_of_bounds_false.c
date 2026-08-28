extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__noreturn__));

void reach_error(void) {
    __assert_fail("0", "error_before_out_of_bounds_false.c", 5, "reach_error");
}

extern unsigned int __VERIFIER_nondet_uint(void);

void __VERIFIER_assert(int condition) {
    if (!condition) {
        reach_error();
    }
}

int main(void) {
    int array[2];
    unsigned int index = __VERIFIER_nondet_uint();

    __VERIFIER_assert(index < 2);
    array[index] = 0;
    return 0;
}
