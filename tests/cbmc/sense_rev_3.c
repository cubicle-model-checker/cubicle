#include <pthread.h>

void fence() {asm("sync");}

int F1 = 0, F2 = 0, F3 = 0, CS = 0;

void * thr0(void *p)
{
    for (;;)
    {
	CS = 1; assert(CS == 1);
	F1 = 1;
	while (F2 != 1 || F3 != 1);
	F1 = 0;
	while (F2 != 0 || F3 != 0);
    }
}

void * thr1(void *p)
{
    for (;;)
    {
	F2 = 1;
	while (F1 != 1 || F3 != 1);
	CS = 2;
	F2 = 0;
	while (F1 != 0 || F3 != 0);
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	F3 = 1;
	while (F1 != 1 || F2 != 1);
	CS = 3;
	F3 = 0;
	while (F1 != 0 || F2 != 0);
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    pthread_create(NULL, NULL, thr2, NULL);
    return 0;
}
