#include <stdio.h>
#include <stdlib.h>

void SigMismatch_Handler(void) {
    printf("An error occurred and the signature value was different from expected");
    exit(-1);
}

int main() {
    int a = 10;
    int b = 20;
    printf("a + b %d", a+b);
    return 0;
}
