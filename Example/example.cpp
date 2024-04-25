#include <assert.h>

//int max(int a, int b)
//{
//    if (a > b)
//        return a;
//    else
//        return b;
//}

//void max(int a, int b)
//{
//    int c;
//    if (a > b)
//        c = a;
//    else
//        c = b;
//
//    assert(c < a || c < b);
//}


//void fun() 
//{
//	int x = 1;
//	int y = 0;
//
//	while (y < 10) {
//		x = x + y;
//		y = y + 1;
//	}
//
//	assert(x > y);
//}

//int add(int f)
//{
//    int y, z;
//    y = f;
//
//    for (int i = 1; i < 10; ++i)
//    {
//        z = y + i;
//        y = z;
//    }
//    
//    return y;
//}

//int main(int argc, char* argv[])
//{
//    int i = 1;
//    int j = 2;
//    int k = max(i, j);
//    return 0;
//}

int foo(int x,int y) {
	auto res = x + y;
	return res;
}

int bar(int x, int y) {		// 11, 1
	auto res = x - y;	//10
	assert(x >= 0 && y >= 0); //&& x < res));
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
