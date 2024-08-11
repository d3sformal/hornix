#include <assert.h>

int bar(int x, int y) {		// 10, 1
	auto res = x - y;	//9
	assert(x >= 0);
	return res;
}

int main() {
	auto x = 10;
	auto y = 1;
	y = bar(x, y);
	assert(x == 10 && y == 9);
	return 0;
}
