#include <pthread.h>

void fence() {asm("sync");}

int F1 = 0, F2 = 0, F3 = 0, F4 = 0, F5 = 0, F6 = 0, F7 = 0, CS = 0;

void * thr0(void *p)
{
    for (;;)
    {
	CS = 1; assert(CS == 1);
	F1 = 1;
	while (F2 != 1 || F3 != 1 || F4 != 1 || F5 != 1 || F6 != 1 || F7 != 1);
	F1 = 0;
	while (F2 != 0 || F3 != 0 || F4 != 0 || F5 != 0 || F6 != 0 || F7 != 0);
    }
}

void * thr1(void *p)
{
    for (;;)
    {
	F2 = 1;
	while (F1 != 1 || F3 != 1 || F4 != 1 || F5 != 1 || F6 != 1 || F7 != 1);
	CS = 2;
	F2 = 0;
	while (F1 != 0 || F3 != 0 || F4 != 0 || F5 != 0 || F6 != 0 || F7 != 0);
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	F3 = 1;
	while (F1 != 1 || F2 != 1 || F4 != 1 || F5 != 1 || F6 != 1 || F7 != 1);
	CS = 3;
	F3 = 0;
	while (F1 != 0 || F2 != 0 || F4 != 0 || F5 != 0 || F6 != 0 || F7 != 0);
    }
}

void * thr3(void *p)
{
    for (;;)
    {
	F4 = 1;
	while (F1 != 1 || F2 != 1 || F3 != 1 || F5 != 1 || F6 != 1 || F7 != 1);
	CS = 4;
	F4 = 0;
	while (F1 != 0 || F2 != 0 || F3 != 0 || F5 != 0 || F6 != 0 || F7 != 0);
    }
}

void * thr4(void *p)
{
    for (;;)
    {
	F5 = 1;
	while (F1 != 1 || F2 != 1 || F3 != 1 || F4 != 1 || F6 != 1 || F7 != 1);
	CS = 5;
	F5 = 0;
	while (F1 != 0 || F2 != 0 || F3 != 0 || F4 != 0 || F6 != 0 || F7 != 0);
    }
}

void * thr5(void *p)
{
    for (;;)
    {
	F6 = 1;
	while (F1 != 1 || F2 != 1 || F3 != 1 || F4 != 1 || F5 != 1 || F7 != 1);
	CS = 6;
	F6 = 0;
	while (F1 != 0 || F2 != 0 || F3 != 0 || F4 != 0 || F5 != 0 || F7 != 0);
    }
}

void * thr6(void *p)
{
    for (;;)
    {
	F7 = 1;
	while (F1 != 1 || F2 != 1 || F3 != 1 || F4 != 1 || F5 != 1 || F6 != 1);
	CS = 7;
	F7 = 0;
	while (F1 != 0 || F2 != 0 || F3 != 0 || F4 != 0 || F5 != 0 || F6 != 0);
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
    return 0;
}
