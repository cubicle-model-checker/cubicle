
#include <stdio.h>
#include <pthread.h>

// Peterson-specific variables
int Want_1 = 0;
int Want_2 = 0;
int Turn = 0;

// Shared counter
int counter = 0;

// Thread 1 Code
void * thread_1(void *p)
{
    int i;
    for (i = 0; i < 1000; i++)
    {
	// Acquire Lock
        Want_1 = 1; Turn = 2;
	while ((Want_2 == 1) && (Turn == 2));

	// Critical Section
	counter++;

	// Release Lock
	Want_1 = 0;
    }
    return NULL;
}

// Thread 2 Code
void * thread_2(void *p)
{
    int i;
    for (i = 0; i < 1000; i++)
    {
	// Acquire Lock
	Want_2 = 1; Turn = 1;
	while ((Want_1 == 1) && (Turn == 1));

	// Critical Section
	counter--;

	// Release Lock
	Want_2 = 0;
    }
    return NULL;
}

// Entry point
int main()
{
    pthread_t th1, th2;
    pthread_create(&th1, NULL, thread_1, NULL);
    pthread_create(&th2, NULL, thread_2, NULL);
    pthread_join(th1, NULL);
    pthread_join(th2, NULL);
    printf("counter = %d\n", counter);
    return 0;
}
