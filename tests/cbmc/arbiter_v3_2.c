
#include <pthread.h>
#include <assert.h>

int CS ;
int Attn1 = 0, Attn2 = 0;
int Answ1 = 0, Answ2 = 0;
int Chng0 = 0, Chng1 = 0, Chng2 = 0;

void * arbiter(void *p)
{
    for (;;)
    {
	if (Attn1 != 0)
	{
	    Chng0 = 1;
	    Answ1 = 1;
	    Chng0 = 0;
	    while (Chng1 != 0);
	    while (Attn1 != 0);
	    Chng0 = 1;
	    Answ1 = 0;
	    Chng0 = 0;
	    while (Chng1 != 0);
	}
	if (Attn2 != 0)
	{
	    Chng0 = 1;
	    Answ2 = 1;
	    Chng0 = 0;
	    while (Chng2 != 0);
	    while (Attn2 != 0);
	    Chng0 = 1;
	    Answ2 = 0;
	    Chng0 = 0;
	    while (Chng2 != 0);
	}
    }
}

void * thr1(void *p)
{
    for (;;)
    {
	while (Answ1 != 0);
	Chng1 = 1;
	Attn1 = 1;
	Chng1 = 0;
	while (Chng0 != 0);
	while (Answ1 == 0);

	/* Critical Section */
	CS = 1;
	assert(CS == 1);

	while (Chng0 != 0);
	Chng1 = 1;
    	Attn1 = 0;
	Chng1 = 0;
    }
}

void * thr2(void *p)
{
    for (;;)
    {
	while (Answ2 != 0);
	Chng2 = 1;
	Attn2 = 1;
	Chng2 = 0;
	while (Chng0 != 0);
	while (Answ2 == 0);

	/* Critical Section */
	CS = 2;
	assert(CS == 2);

	while (Chng0 != 0);
	Chng2 = 1;
    	Attn2 = 0;
	Chng2 = 0;
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
