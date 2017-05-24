#include <pthread.h>

int Want1, Want2, Turn, CS;

void * thr0(void *p)
{
    for (;;)
    {
	Want1 = 1;
	while (Want2 == 1)
	{
	    if (Turn != 1)
	    {
		Want1 = 0;
		while (Turn != 1);
		Want1 = 1;
	    }
	}

	/* Critical Section */
	CS = 1;
	assert(CS == 1);
	
	Turn = 2;
	Want1 = 0;
    }
}
void * thr1(void *p)
{
    for (;;)
    {
	Want2 = 1;
	while (Want1 == 1)
	{
	    if (Turn != 2)
	    {
		Want2 = 0;
		while (Turn != 2);
		Want2 = 1;
	    }
	}

	/* Critical Section */
	CS = 2;
	assert(CS == 2);

	Turn = 1;
	Want2 = 0;
    }
}

int main()
{
    pthread_create(NULL, NULL, thr0, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    return 0;
}
