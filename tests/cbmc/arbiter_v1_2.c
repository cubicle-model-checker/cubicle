
#include <pthread.h>
#include <assert.h>

int CS ;
int Attn1 = 0, Attn2 = 0;
int Leaving = 0;

void * arbiter(void *p)
{
    for (;;)
    {
	if (Attn1 != 0)
	{
	    Attn1 = 0;
	    while (Leaving == 0);
	    Leaving = 0;
	}
	if (Attn2 != 0)
	{
	    Attn2 = 0;
	    while (Leaving == 0);
	    Leaving = 0;
	}
    }
}

void * thr1(void *p)
{
    for (;;)
    {
	Attn1 = 1;
	while (Attn1 != 0);

	/* Critical Section */
	CS = 1;
	assert(CS == 1);

    	Leaving = 1;
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	Attn2 = 1;
	while (Attn2 != 0);

	/* Critical Section */
	CS = 2;
	assert(CS == 2);

    	Leaving = 1;
    }
}

int main()
{
    pthread_t th[3];
    pthread_create(&th[0], NULL, arbiter, NULL);
    pthread_create(&th[1], NULL, thr1, NULL);
    pthread_create(&th[2], NULL, thr2, NULL);
    pthread_join(th[0], NULL);
    pthread_join(th[1], NULL);
    pthread_join(th[2], NULL);
    return 0;
}
