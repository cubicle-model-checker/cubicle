
#include <pthread.h>
#include <assert.h>

_Bool nondet_bool();

enum msi { M = 2, S = 1, I = 0 };

enum msi C1, C2 = I;

pthread_mutex_t lock;

void * thrchk(void *p)
{
    for (;;)
    {
        pthread_mutex_lock(&lock);
	assert(!(C1 == M && C2 != I || C1 != I && C2 == M));
	pthread_mutex_unlock(&lock);
    }
}

void * thr1(void *p)
{
    for (;;)
    {
        if (nondet_bool()) {
	    pthread_mutex_lock(&lock);
	    if (C1 == I) {
	        C1 = S;
	        if (C2 == M) C2 = S;
	    }
	    pthread_mutex_unlock(&lock);
	}
	else {
	    pthread_mutex_lock(&lock);
	    if (C1 != M) {
	        C1 = M;
	        C2 = I;
	    }
	    pthread_mutex_unlock(&lock);
	}
    }
}

void * thr2(void *p)
{
    for (;;)
    {
        if (nondet_bool()) {
	    pthread_mutex_lock(&lock);
	    if (C2 == I) {
	        C2 = S;
	        if (C1 == M) C1 = S;
	    } 
	    pthread_mutex_unlock(&lock);
	}
	else {
	    pthread_mutex_lock(&lock);
	    if (C2 != M) {
	        C2 = M;
	        C1 = I;
	    }
	    pthread_mutex_unlock(&lock);
        }
    }
}

int main()
{
    pthread_mutex_init(&lock, NULL);
    pthread_create(NULL, NULL, thrchk, NULL);
    pthread_create(NULL, NULL, thr1, NULL);
    pthread_create(NULL, NULL, thr2, NULL);
    return 0;
}
