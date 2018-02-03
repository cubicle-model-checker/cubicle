#include <pthread.h>
#include <assert.h>

void fence() {asm("sync");}

pthread_mutex_t mut;
int lock = 1, CS = 0;

void * thr(void *p)
{
    int l, id = *(int *)p;
    for (;;)
    {
	pthread_mutex_lock(&mut);
	l = lock--;
	pthread_mutex_unlock(&mut);
	if (l <= 0) { // Spin
	    while (lock <= 0);
	    continue;
	}
	else { // Critical section
	    CS = id;
	    assert(CS == id);
	    lock = 1;
	}
    }
}

int main()
{
    int id[3] = { 1, 2, 3 };
    pthread_mutex_init(&mut, NULL);
    pthread_create(NULL, NULL, thr, &id[0]);
    pthread_create(NULL, NULL, thr, &id[1]);
    pthread_create(NULL, NULL, thr, &id[2]);
    return 0;
}
