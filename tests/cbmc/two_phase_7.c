
#include <pthread.h>
#include <assert.h>

enum state { Unknown, ReadyCommit, ReadyAbort, Committed, Aborted };

enum state Astate1 = Unknown, Astate2 = Unknown,
           Astate3 = Unknown, Astate4 = Unknown,
           Astate5 = Unknown, Astate6 = Unknown,
           Astate7 = Unknown;
enum state Cstate = Unknown;

void safety_prop()
{
    assert(!(
      Astate1 == Committed && Astate2 == Aborted ||
      Astate1 == Committed && Astate3 == Aborted ||
      Astate1 == Committed && Astate4 == Aborted ||
      Astate1 == Committed && Astate5 == Aborted ||
      Astate1 == Committed && Astate6 == Aborted ||
      Astate1 == Committed && Astate7 == Aborted ||
      Astate2 == Committed && Astate3 == Aborted ||
      Astate2 == Committed && Astate4 == Aborted ||
      Astate2 == Committed && Astate5 == Aborted ||
      Astate2 == Committed && Astate6 == Aborted ||
      Astate2 == Committed && Astate7 == Aborted ||
      Astate3 == Committed && Astate4 == Aborted ||
      Astate3 == Committed && Astate5 == Aborted ||
      Astate3 == Committed && Astate6 == Aborted ||
      Astate3 == Committed && Astate7 == Aborted ||
      Astate4 == Committed && Astate5 == Aborted ||
      Astate4 == Committed && Astate6 == Aborted ||
      Astate4 == Committed && Astate7 == Aborted ||
      Astate5 == Committed && Astate6 == Aborted ||
      Astate5 == Committed && Astate7 == Aborted ||
      Astate6 == Committed && Astate7 == Aborted ||
      Astate1 == Aborted && Astate2 == Committed ||
      Astate1 == Aborted && Astate3 == Committed ||
      Astate1 == Aborted && Astate4 == Committed ||
      Astate1 == Aborted && Astate5 == Committed ||
      Astate1 == Aborted && Astate6 == Committed ||
      Astate1 == Aborted && Astate7 == Committed ||
      Astate2 == Aborted && Astate3 == Committed ||
      Astate2 == Aborted && Astate4 == Committed ||
      Astate2 == Aborted && Astate5 == Committed ||
      Astate2 == Aborted && Astate6 == Committed ||
      Astate2 == Aborted && Astate7 == Committed ||
      Astate3 == Aborted && Astate4 == Committed ||
      Astate3 == Aborted && Astate5 == Committed ||
      Astate3 == Aborted && Astate6 == Committed ||
      Astate3 == Aborted && Astate7 == Committed ||
      Astate4 == Aborted && Astate5 == Committed ||
      Astate4 == Aborted && Astate6 == Committed ||
      Astate4 == Aborted && Astate7 == Committed ||
      Astate5 == Aborted && Astate6 == Committed ||
      Astate5 == Aborted && Astate7 == Committed ||
      Astate6 == Aborted && Astate7 == Committed
    ));
}

void * thr0(void *p)
{
    for (;;)
    {
	if (Astate1 == ReadyCommit && Astate2 == ReadyCommit &&
	    Astate3 == ReadyCommit && Astate4 == ReadyCommit &&
	    Astate5 == ReadyCommit && Astate6 == ReadyCommit &&
	    Astate7 == ReadyCommit)
	{
	    Cstate = Committed;
	}
	else if (Astate1 == ReadyAbort || Astate2 == ReadyAbort ||
		 Astate3 == ReadyAbort || Astate4 == ReadyAbort ||
		 Astate5 == ReadyAbort || Astate6 == ReadyAbort ||
		 Astate7 == ReadyAbort)
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
    safety_prop();
}

void * thr2(void *p)
{
    Astate2 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate2 = Cstate;
    safety_prop();
}

void * thr3(void *p)
{
    Astate3 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate3 = Cstate;
    safety_prop();
}

void * thr4(void *p)
{
    Astate4 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate4 = Cstate;
    safety_prop();
}

void * thr5(void *p)
{
    Astate5 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate5 = Cstate;
    safety_prop();
}

void * thr6(void *p)
{
    Astate6 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate6 = Cstate;
    safety_prop();
}

void * thr7(void *p)
{
    Astate7 = (nondet_int() % 2 == 0) ? ReadyCommit : ReadyAbort;
    while (Cstate == Unknown);
    Astate7 = Cstate;
    safety_prop();
}

int main()
{
    pthread_t th[7];
    pthread_create(&th[0], NULL, thr0, NULL);
    pthread_create(&th[1], NULL, thr1, NULL);
    pthread_create(&th[2], NULL, thr2, NULL);
    pthread_create(&th[3], NULL, thr3, NULL);
    pthread_create(&th[4], NULL, thr4, NULL);
    pthread_create(&th[5], NULL, thr5, NULL);
    pthread_create(&th[6], NULL, thr6, NULL);
    pthread_create(&th[7], NULL, thr7, NULL);
    pthread_join(th[0], NULL);
    pthread_join(th[1], NULL);
    pthread_join(th[2], NULL);
    pthread_join(th[3], NULL);
    pthread_join(th[4], NULL);
    pthread_join(th[5], NULL);
    pthread_join(th[6], NULL);
    pthread_join(th[7], NULL);
    return 0;
}
