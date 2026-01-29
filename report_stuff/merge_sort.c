#include <stdlib.h>
#include <time.h>
#include <assert.h>
#define LEN 100000

void merge_sort(int array[], int start, int end);
void merge(int array[], int start, int end, int middle);

int main() {
    srand(time(0));
    int array[LEN];

    for (int i = 0; i < LEN; i++) {
	array[i] = rand() % (2*LEN);
    }

    merge_sort(array, 0, LEN);

    int correct = 1;
    for (int i = 0; i < LEN-1 && correct; i++) {
    	if(array[i+1] < array[i]) correct = 0;
    }

    assert(correct);
    return 0;
}

void merge_sort(int array[], int start, int end) {
    if (start + 1 >= end) return;

    int middle = (start + end) / 2;
    merge_sort(array, start, middle);
    merge_sort(array, middle, end);
    merge(array, start, end, middle);
}

void merge(int array[], int start, int end, int middle) {
    int *aux_arr = (int*) malloc(sizeof(int)*(end-start)); 

    if (!aux_arr) {
	exit(-1);
    }

    for(int k = 0, i = start; k < end - start; k++, i++) {
	aux_arr[k] = array[i];
    }

    int i = 0;
    int j = middle-start;
    for(int k = start; k < end; k++) {
	if (j >= end-start || (i < middle-start && aux_arr[i] < aux_arr[j])) {
	    array[k] = aux_arr[i];
	    i++;
	} else {
	    array[k] = aux_arr[j];
	    j++;
	}
    }

    free(aux_arr);
}
