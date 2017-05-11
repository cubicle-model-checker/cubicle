#include <pthread.h>
int x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, tid;

void *thr0() {
  int cond = 0, counter = 0, thread_id = 0;
  goto lq0;
  lq0:
    cond = x0; goto lq1;
  lq2:
    /* critical section */
    tid = thread_id;
    if (tid!=thread_id) ERROR: goto ERROR;;
    counter = x1; goto lq3;
  lq1:
    if (cond != 0) goto lfinish;
    if (cond == 0) goto lq2;
  lfinish:
    goto done;
  lq3:
    x1 = 0; goto lq0;
  done: return 0;
}
void *thr1() {
  int r = 0, thread_id = 1;
  goto lq0;
  lq0:
    x0 = 1; goto lq1;
  lq5:
    /* critical section */
    tid = thread_id;
    if (tid!=thread_id) ERROR: goto ERROR;;
    goto done;
  lq1:
    /* mfence */ goto lq2;
  lq2:
    x1 = 1; goto lq3;
  lq3:
    r = x1; goto lq4;
  lq4:
    if (r == 0) goto lq5;
  done: return 0;
}
int main() {
  pthread_t t0, t1;

  pthread_create(&t0, 0, thr0, 0);
  pthread_create(&t1, 0, thr1, 0);
  pthread_join(&t0, 0);
  pthread_join(&t1, 0);

  return 0;
}
