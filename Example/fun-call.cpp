#include <assert.h>

int inc(int x) {
	return x + 1;
}


int main() {
	int a = 0;
	a = inc(a);
	//int b = a + 2;
	//b = b + 3;
	assert(a == 1);
	return 0;
}