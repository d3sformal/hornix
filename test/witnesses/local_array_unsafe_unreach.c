extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((noreturn));
extern int __VERIFIER_nondet_int(void);

void reach_error(void) {
    __assert_fail("0", "local_array_unsafe_unreach.c", 5, "reach_error");
}

int main(void) {
    int length = __VERIFIER_nondet_int();
    if (length < 1 || length > 4) { return 0; }

    int values[length];
    values[0] = 1;
    if (values[0] == 1) { reach_error(); }
    return 0;
}
