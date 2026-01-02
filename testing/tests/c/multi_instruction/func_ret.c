#include <stdio.h>
#include <stdlib.h>

void SigMismatch_Handler(void) {
    printf("An error occurred and the signature value was different from expected");
    exit(-1);
}

int foo();

int main() {
    int a = 10;
    int b = 20;
    int c = foo();
    printf("foo() %d", c);
    return a > b ? a : b;
}

int foo() {
    int c = 12;
    int d = 13;
    return c + d;
}
