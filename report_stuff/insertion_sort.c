#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>
#define LEN 10000

int main() {
    srand(time(0));
    int array[LEN];

    for(int i = 0; i < LEN; i++) {
	array[i] = rand() % (2*LEN);
    }

    for(int i = 0; i < LEN-1; i++)
	for(int j = i+1; j > 0; j--) {
	    if(array[j] < array[j-1]){
		array[j] = array[j]^array[j-1];
		array[j-1] ^= array[j];
		array[j] ^= array[j-1];
	    }
	}

    int correct = 1;
    for(int i = 0; i < LEN-1 && correct; i++) {
	if(array[i+1] < array[i]) correct = 0;
    }
    
    // assert(correct);
    printf("%s", correct == 1 ? "true" : "false");
    return 0;
}
