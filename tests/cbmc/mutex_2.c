#include <pthread.h>

void fence() {asm("sync");}

int R1, R2 = 0, CS;

void * thr0(void *p)
{
    for (;;)
    {
	R1 = 1;
	fence();
	while (R2 != 0);
	/* Critical Section */
	CS = 1;
	assert(CS == 1);	
	R1 = 0;
    }
}

void * thr1(void *p)
{
    for (;;)
    {
	R2 = 1;
	fence();
	while (R1 != 0);
	/* Critical Section */
	CS = 2;
	assert(CS == 2);	
	R2 = 0;
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    return 0;
}
