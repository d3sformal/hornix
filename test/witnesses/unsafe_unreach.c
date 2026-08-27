extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((noreturn));

void reach_error(void);

int main(void) {
    reach_error();
}

void reach_error(void) {
    __assert_fail("reach_error", "unsafe_unreach.c", 9, "reach_error");
}

/* This mention must not be mistaken for a call: reach_error(); */
