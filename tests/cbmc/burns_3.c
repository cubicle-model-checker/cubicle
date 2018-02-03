#include <pthread.h>

void fence() {asm("sync");}

int F[3] = { 0, 0, 0}, CS;

void * thr0(void *p)
{
    for (;;)
    {
	F[0] = 0;
	fence();
	F[0] = 1;
	fence();
	while (F[1] == 1 || F[2] == 1);

	/* Critical Section */
	CS = 1;
	assert(CS == 1);
    }
}
void * thr1(void *p)
{
    for (;;)
    {
	F[1] = 0;
	fence();
	if (F[0] == 1) continue;
	F[1] = 1;
	fence();
	if (F[0] == 1) continue;
	while (F[2] == 1);

	/* Critical Section */
	CS = 2;
	assert(CS == 2);
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	F[2] = 0;
	fence();
	if (F[0] == 1 || F[1] == 1) continue;
	F[2] = 1;
	fence();
	if (F[0] == 1 || F[1] == 1) continue;

	/* Critical Section */
	CS = 3;
	assert(CS == 3);
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    pthread_create(NULL, NULL, thr2, NULL);
    return 0;
}
