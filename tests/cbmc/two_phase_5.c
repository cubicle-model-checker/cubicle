
#include <pthread.h>
#include <assert.h>

enum state { Unknown, ReadyCommit, ReadyAbort, Committed, Aborted };

enum state Astate1 = Unknown, Astate2 = Unknown,
           Astate3 = Unknown, Astate4 = Unknown,
           Astate5 = Unknown;
enum state Cstate = Unknown;

void * thr0(void *p)
{
    for (;;)
    {
	if (Astate1 == ReadyCommit && Astate2 == ReadyCommit &&
	    Astate3 == ReadyCommit && Astate4 == ReadyCommit &&
	    Astate5 == ReadyCommit)
	{
	    Cstate = Committed;
	}
	else if (Astate1 == ReadyAbort || Astate2 == ReadyAbort ||
		 Astate3 == ReadyAbort || Astate4 == ReadyAbort ||
		 Astate5 == ReadyAbort)
	{
	    Cstate = Aborted;
	}
    }
}

void * thr1(void *p)
{
    Astate1 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate1 = Cstate;

    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Committed && Astate3 == Aborted ||
      Astate1 == Committed && Astate4 == Aborted ||
      Astate1 == Committed && Astate5 == Aborted ||
      Astate2 == Committed && Astate3 == Aborted ||
      Astate2 == Committed && Astate4 == Aborted ||
      Astate2 == Committed && Astate5 == Aborted ||
      Astate3 == Committed && Astate4 == Aborted ||
      Astate3 == Committed && Astate5 == Aborted ||
      Astate4 == Committed && Astate5 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed ||
      Astate1 == Aborted && Astate3 == Committed ||
      Astate1 == Aborted && Astate4 == Committed ||
      Astate1 == Aborted && Astate5 == Committed ||
      Astate2 == Aborted && Astate3 == Committed ||
      Astate2 == Aborted && Astate4 == Committed ||
      Astate2 == Aborted && Astate5 == Committed ||
      Astate3 == Aborted && Astate4 == Committed ||
      Astate3 == Aborted && Astate5 == Committed ||
      Astate4 == Aborted && Astate5 == Committed
    ));
}

void * thr2(void *p)
{
    Astate2 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate2 = Cstate;

    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Committed && Astate3 == Aborted ||
      Astate1 == Committed && Astate4 == Aborted ||
      Astate1 == Committed && Astate5 == Aborted ||
      Astate2 == Committed && Astate3 == Aborted ||
      Astate2 == Committed && Astate4 == Aborted ||
      Astate2 == Committed && Astate5 == Aborted ||
      Astate3 == Committed && Astate4 == Aborted ||
      Astate3 == Committed && Astate5 == Aborted ||
      Astate4 == Committed && Astate5 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed ||
      Astate1 == Aborted && Astate3 == Committed ||
      Astate1 == Aborted && Astate4 == Committed ||
      Astate1 == Aborted && Astate5 == Committed ||
      Astate2 == Aborted && Astate3 == Committed ||
      Astate2 == Aborted && Astate4 == Committed ||
      Astate2 == Aborted && Astate5 == Committed ||
      Astate3 == Aborted && Astate4 == Committed ||
      Astate3 == Aborted && Astate5 == Committed ||
      Astate4 == Aborted && Astate5 == Committed
    ));
}

void * thr3(void *p)
{
    Astate3 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate3 = Cstate;

    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Committed && Astate3 == Aborted ||
      Astate1 == Committed && Astate4 == Aborted ||
      Astate1 == Committed && Astate5 == Aborted ||
      Astate2 == Committed && Astate3 == Aborted ||
      Astate2 == Committed && Astate4 == Aborted ||
      Astate2 == Committed && Astate5 == Aborted ||
      Astate3 == Committed && Astate4 == Aborted ||
      Astate3 == Committed && Astate5 == Aborted ||
      Astate4 == Committed && Astate5 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed ||
      Astate1 == Aborted && Astate3 == Committed ||
      Astate1 == Aborted && Astate4 == Committed ||
      Astate1 == Aborted && Astate5 == Committed ||
      Astate2 == Aborted && Astate3 == Committed ||
      Astate2 == Aborted && Astate4 == Committed ||
      Astate2 == Aborted && Astate5 == Committed ||
      Astate3 == Aborted && Astate4 == Committed ||
      Astate3 == Aborted && Astate5 == Committed ||
      Astate4 == Aborted && Astate5 == Committed
    ));
}

void * thr4(void *p)
{
    Astate4 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate4 = Cstate;

    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Committed && Astate3 == Aborted ||
      Astate1 == Committed && Astate4 == Aborted ||
      Astate1 == Committed && Astate5 == Aborted ||
      Astate2 == Committed && Astate3 == Aborted ||
      Astate2 == Committed && Astate4 == Aborted ||
      Astate2 == Committed && Astate5 == Aborted ||
      Astate3 == Committed && Astate4 == Aborted ||
      Astate3 == Committed && Astate5 == Aborted ||
      Astate4 == Committed && Astate5 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed ||
      Astate1 == Aborted && Astate3 == Committed ||
      Astate1 == Aborted && Astate4 == Committed ||
      Astate1 == Aborted && Astate5 == Committed ||
      Astate2 == Aborted && Astate3 == Committed ||
      Astate2 == Aborted && Astate4 == Committed ||
      Astate2 == Aborted && Astate5 == Committed ||
      Astate3 == Aborted && Astate4 == Committed ||
      Astate3 == Aborted && Astate5 == Committed ||
      Astate4 == Aborted && Astate5 == Committed
    ));
}

void * thr5(void *p)
{
    Astate5 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate5 = Cstate;

    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Committed && Astate3 == Aborted ||
      Astate1 == Committed && Astate4 == Aborted ||
      Astate1 == Committed && Astate5 == Aborted ||
      Astate2 == Committed && Astate3 == Aborted ||
      Astate2 == Committed && Astate4 == Aborted ||
      Astate2 == Committed && Astate5 == Aborted ||
      Astate3 == Committed && Astate4 == Aborted ||
      Astate3 == Committed && Astate5 == Aborted ||
      Astate4 == Committed && Astate5 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed ||
      Astate1 == Aborted && Astate3 == Committed ||
      Astate1 == Aborted && Astate4 == Committed ||
      Astate1 == Aborted && Astate5 == Committed ||
      Astate2 == Aborted && Astate3 == Committed ||
      Astate2 == Aborted && Astate4 == Committed ||
      Astate2 == Aborted && Astate5 == Committed ||
      Astate3 == Aborted && Astate4 == Committed ||
      Astate3 == Aborted && Astate5 == Committed ||
      Astate4 == Aborted && Astate5 == Committed
    ));
}

int main()
{
    pthread_t th[5];
    pthread_create(&th[0], NULL, thr0, NULL);
    pthread_create(&th[1], NULL, thr1, NULL);
    pthread_create(&th[2], NULL, thr2, NULL);
    pthread_create(&th[3], NULL, thr3, NULL);
    pthread_create(&th[4], NULL, thr4, NULL);
    pthread_create(&th[5], NULL, thr5, NULL);
    pthread_join(th[0], NULL);
    pthread_join(th[1], NULL);
    pthread_join(th[2], NULL);
    pthread_join(th[3], NULL);
    pthread_join(th[4], NULL);
    pthread_join(th[5], NULL);
    return 0;
}
