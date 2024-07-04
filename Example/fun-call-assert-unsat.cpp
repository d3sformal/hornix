#include <assert.h>

int foo(int x,int y) {
	auto res = x + y;
	return res;
}

int bar(int x, int y) {		// 11, 1
	auto res = x - y;				//10
	assert(x >= 0 && y >= 0 && x < res);
	return res;
}

int main() {
	auto x = 10;
	auto y = 1;
	auto xold = x;	//10
	auto yold = y;	//1
	x = foo(x, y);	//11 = 10 + 1
	y = bar(x, y);	//10 = 11 - 1
	x = bar(x, y);	//1 = 11 - 10
	assert(x == yold && y == xold);
	return 0;
}
