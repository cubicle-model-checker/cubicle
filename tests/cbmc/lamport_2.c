#include <pthread.h>

void fence() {asm("sync");}

int X, Y = 0, CS;

void * thr0(void *p)
{
    for (;;)
    {
	do
	{
	    X = 1;
	    fence();	
	} while (Y != 0);
	Y = 1;
	fence();
	if (X != 1)
	{
	    if (Y != 1) continue;
	    for (;;);
	}

	/* Critical Section */
	CS = 1;
	assert(CS == 1);
	
	Y = 0;
    }
}
void * thr1(void *p)
{
    for (;;)
    {
	do
	{
	    X = 2;
	    fence();	
	} while (Y != 0);
	Y = 2;
	fence();
	if (X != 2)
	{
	    if (Y != 2) continue;
	    for (;;);
	}

	/* Critical Section */
	CS = 2;
	assert(CS == 2);
	
	Y = 0;
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    return 0;
}
