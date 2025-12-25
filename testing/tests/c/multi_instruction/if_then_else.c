#include <stdio.h>

int main() {
    int a = 10;
    int b = 20;
    int c = a + b;
    a = 12;
    b = 13;
    int d = a + b;
    if(c > d) {
	a = 15;
	b = 2;
	d = a + b;
    } else {
	a = 13;
	b = 19;
	c = a + b;
    }

    printf("c: %d d: %d\n", c, d);
    return 0;
}
