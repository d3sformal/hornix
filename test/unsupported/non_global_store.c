extern void *malloc(unsigned long);

int main(void) {
    int * p = malloc(sizeof(int));
    *p = 1;
    return 0;
}
