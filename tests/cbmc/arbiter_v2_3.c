
#include <pthread.h>
#include <assert.h>

int CS ;
int Attn1 = 0, Attn2 = 0, Attn3 = 0;
int Answ1 = 0, Answ2 = 0, Answ3 = 0;

void * arbiter(void *p)
{
    for (;;)
    {
	if (Attn1 != 0)
	{
	    Answ1 = 1;
	    while (Attn1 != 0);
	    Answ1 = 0;
	}
	if (Attn2 != 0)
	{
	    Answ2 = 1;
	    while (Attn2 != 0);
	    Answ2 = 0;
	}
	if (Attn3 != 0)
	{
	    Answ3 = 1;
	    while (Attn3 != 0);
	    Answ3 = 0;
	}
    }
}

void * thr1(void *p)
{
    for (;;)
    {
	while (Answ1 != 0);
	Attn1 = 1;
	while (Answ1 == 0);

	/* Critical Section */
	CS = 1;
	assert(CS == 1);

    	Attn1 = 0;
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	while (Answ2 != 0);
	Attn2 = 1;
	while (Answ2 == 0);

	/* Critical Section */
	CS = 2;
	assert(CS == 2);

    	Attn2 = 0;
    }
}

void * thr3(void *p)
{
    for (;;)
    {
	while (Answ3 != 0);
	Attn3 = 1;
	while (Answ3 == 0);

	/* Critical Section */
	CS = 3;
	assert(CS == 3);

    	Attn3 = 0;
    }
}

int main()
{
    pthread_t th[4];
    pthread_create(&th[0], NULL, arbiter, NULL);
    pthread_create(&th[1], NULL, thr1, NULL);
    pthread_create(&th[2], NULL, thr2, NULL);
    pthread_create(&th[3], NULL, thr3, NULL);
    pthread_join(th[0], NULL);
    pthread_join(th[1], NULL);
    pthread_join(th[2], NULL);
    pthread_join(th[3], NULL);
    return 0;
}
