#include <pthread.h>

void fence() {asm("sync");}

int R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11 = 0, CS;

void * thr0(void *p)
{
    for (;;)
    {
	R1 = 1;
	while (R2 != 0 || R3 != 0 || R4 != 0 || R5 != 0 ||
	       R6 != 0 || R7 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
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
	while (R1 != 0 || R3 != 0 || R4 != 0 || R5 != 0 ||
	       R6 != 0 || R7 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 2;
	assert(CS == 2);	
	R2 = 0;
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	R3 = 1;
	while (R1 != 0 || R2 != 0 || R4 != 0 || R5 != 0 ||
	       R6 != 0 || R7 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 3;
	assert(CS == 3);	
	R3 = 0;
    }
}

void * thr3(void *p)
{
    for (;;)
    {
	R4 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R5 != 0 ||
	       R6 != 0 || R7 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 4;
	assert(CS == 4);	
	R4 = 0;
    }
}

void * thr4(void *p)
{
    for (;;)
    {
	R5 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R6 != 0 || R7 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 5;
	assert(CS == 5);	
	R5 = 0;
    }
}

void * thr5(void *p)
{
    for (;;)
    {
	R6 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R5 != 0 || R7 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 6;
	assert(CS == 6);	
	R6 = 0;
    }
}

void * thr6(void *p)
{
    for (;;)
    {
	R7 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R5 != 0 || R6 != 0 || R8 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 7;
	assert(CS == 7);	
	R7 = 0;
    }
}

void * thr7(void *p)
{
    for (;;)
    {
	R8 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R5 != 0 || R6 != 0 || R7 != 0 || R9 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 8;
	assert(CS == 8);
	R8 = 0;
    }
}

void * thr8(void *p)
{
    for (;;)
    {
	R9 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R5 != 0 || R6 != 0 || R7 != 0 || R8 != 0 ||
	       R10 != 0 || R11 != 0);
	/* Critical Section */
	CS = 9;
	assert(CS == 9);
	R9 = 0;
    }
}

void * thr9(void *p)
{
    for (;;)
    {
	R10 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R5 != 0 || R6 != 0 || R7 != 0 || R8 != 0 ||
	       R9 != 0 || R11 != 0);
	/* Critical Section */
	CS = 10;
	assert(CS == 10);
	R10 = 0;
    }
}

void * thr10(void *p)
{
    for (;;)
    {
	R11 = 1;
	while (R1 != 0 || R2 != 0 || R3 != 0 || R4 != 0 ||
	       R5 != 0 || R6 != 0 || R7 != 0 || R8 != 0 ||
	       R9 != 0 || R10 != 0);
	/* Critical Section */
	CS = 11;
	assert(CS == 11);
	R11 = 0;
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    pthread_create(NULL, NULL, thr2, NULL);
    pthread_create(NULL, NULL, thr3, NULL);
    pthread_create(NULL, NULL, thr4, NULL);
    pthread_create(NULL, NULL, thr5, NULL);
    pthread_create(NULL, NULL, thr6, NULL);
    pthread_create(NULL, NULL, thr7, NULL);
    pthread_create(NULL, NULL, thr8, NULL);
    pthread_create(NULL, NULL, thr9, NULL);
    pthread_create(NULL, NULL, thr10, NULL);
    return 0;
}
