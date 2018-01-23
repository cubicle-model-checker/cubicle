
#include <pthread.h>
#include <assert.h>

enum state { Unknown, ReadyCommit, ReadyAbort, Committed, Aborted };

enum state Astate1 = Unknown, Astate2 = Unknown;
enum state Cstate = Unknown;

void * thr0(void *p)
{
    if (Astate1 == ReadyCommit && Astate2 == ReadyCommit)
    {
	Cstate = Committed;
    }
    else if (Astate1 == ReadyAbort || Astate2 == ReadyAbort)
    {
	Cstate = Aborted;
    }
}

void * thr1(void *p)
{
    Astate1 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == 0);
    Astate1 = Cstate;

    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed
    ));
}

void * thr2(void *p)
{
    Astate2 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == 0);
    Astate2 = Cstate;

    assert(!(
        Astate1 == Committed && Astate2 == Aborted ||
	Astate1 == Aborted && Astate2 == Committed
    ));
}

int main()
{
    pthread_t th[3];
    pthread_create(&th[0], NULL, thr0, NULL);
    pthread_create(&th[1], NULL, thr1, NULL);
    pthread_create(&th[2], NULL, thr2, NULL);
    pthread_join(th[0], NULL);
    pthread_join(th[1], NULL);
    pthread_join(th[2], NULL);
    return 0;
}
