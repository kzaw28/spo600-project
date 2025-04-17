// Simple Arithmetic vs. Array Processing
// Functions annotated via CLONE_ATTRIBUTE to drive target_clones from the Makefile

#include <stdio.h>
#include <stdlib.h>

#ifndef CLONE_ATTRIBUTE
#define CLONE_ATTRIBUTE
#endif

// Simple arithmetic function – expected to be PRUNED
CLONE_ATTRIBUTE
int add_numbers(int a, int b) {
    int result = a + b;
    if (result > 100) {
        return result - 50;
    } else {
        return result * 2;
    }
}

// Array-processing function – expected to be NOPRUNED
CLONE_ATTRIBUTE
void process_array(int *arr, int size) {
    for (int i = 0; i < size; i++) {
        if (arr[i] % 2 == 0) {
            arr[i] = arr[i] * 4 + 3;
        } else {
            arr[i] = arr[i] / 2;
        }
    }
}

int main(void) {
    // Test add_numbers
    printf("add_numbers(10,20) = %d\n", add_numbers(10, 20));
    printf("add_numbers(70,50) = %d\n", add_numbers(70, 50));

    // Test process_array
    int array[10] = {1,2,3,4,5,6,7,8,9,10};
    process_array(array, 10);

    printf("Processed array: ");
    for (int i = 0; i < 10; i++)
        printf("%d ", array[i]);
    printf("\n");

    return 0;
}











