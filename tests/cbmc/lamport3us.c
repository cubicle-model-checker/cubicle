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
	} while (Y != 0);
	Y = 1;
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
	} while (Y != 0);
	Y = 2;
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

void * thr2(void *p)
{
    for (;;)
    {
	do
	{
	    X = 3;
	} while (Y != 0);
	Y = 3;
	if (X != 3)
	{
	    if (Y != 3) continue;
	    for (;;);
	}

	/* Critical Section */
	CS = 3;
	assert(CS == 3);
	
	Y = 0;
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    pthread_create(NULL, NULL, thr2, NULL);
    return 0;
}
