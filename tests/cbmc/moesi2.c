
#include <pthread.h>
#include <assert.h>

int nondet_int();

enum msi { M = 4, O = 3, E = 2, S = 1, I = 0 };

enum msi C1, C2 = I;

pthread_mutex_t lock;

void * thrchk(void *p)
{
    for (;;)
    {
        pthread_mutex_lock(&lock);
	assert(!(C1 == M && C2 == M));
	pthread_mutex_unlock(&lock);
    }
}

void * thr1(void *p)
{
    for (;;)
    {
        switch (nondet_int() % 3) {
	  case 0:
	    pthread_mutex_lock(&lock);
	    if (C1 == I) {
	        C1 = S;
	        switch (C2) {
		  case E: C2 = S; break;
	          case M: C2 = O; break;
		}
	    }
	    pthread_mutex_unlock(&lock);
	    break;
	  case 1:
	    pthread_mutex_lock(&lock);
	    if (C1 == E) {
	        C1 = M;
	    }
	    pthread_mutex_unlock(&lock);
	    break;
	  case 2:
	    pthread_mutex_lock(&lock);
	    if (C1 == I || C1 == S || C1 == O) {
	        C1 = E;
	        C2 = I;
	    }
	    pthread_mutex_unlock(&lock);
	    break;
	}
    }
}

void * thr2(void *p)
{
    for (;;)
    {
        switch (nondet_int() % 3) {
	  case 0:
	    pthread_mutex_lock(&lock);
	    if (C2 == I) {
	        C2 = S;
	        switch (C1) {
		  case E: C1 = S; break;
	          case M: C1 = O; break;
		}
	    }
	    pthread_mutex_unlock(&lock);
	    break;
	  case 1:
	    pthread_mutex_lock(&lock);
	    if (C2 == E) {
	        C2 = M;
	    }
	    pthread_mutex_unlock(&lock);
	    break;
	  case 2:
	    pthread_mutex_lock(&lock);
	    if (C2 == I || C2 == S || C2 == O) {
	        C2 = E;
	        C1 = I;
	    }
	    pthread_mutex_unlock(&lock);
	    break;
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
