#include <assert.h>

int bar(int x, int y) {		// 11, 1
	auto res = x - y;	//10
	auto a = 1;
	assert(a >= 0);//&& y >= 0); //&& x < res));
	return res;
}

int main() {
	auto x = 10;
	auto y = 1;
	y = bar(x, y);	//9 = 10 - 1
	//assert(x == 10 && y == 9);
	return 0;
}
