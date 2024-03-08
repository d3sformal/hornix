#include <cassert>

//int max(int a, int b)
//{
//    if (a > b)
//        return a;
//    else
//        return b;
//}

//int max(int a, int b)
//{
//    __int8 c;
//    if (a > b)
//        c = a > b;
//    else
//        c = a > b;
//
//    //assert(c >= a && c >= b);
//    return c;
//}


void fun() 
{
	int x = 1;
	int y = 0;

	while (y < 10) {
		x = x + y;
		y = y + 1;
	}

	assert(x > y);
}

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
