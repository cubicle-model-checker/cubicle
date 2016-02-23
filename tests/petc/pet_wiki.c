#include <stdio.h>
#include <pthread.h>

#define PTHREAD_FUNCTION(fct) (void *(*)(void *))fct

#define FALSE 0
#define  TRUE 1

// Use Peterson's algorithm, 1981
typedef struct {
    // We need an array with same number of slots
    // that we have thread to manage
    int flag[2];
    int turn;
    int shared_value;
} Peterson_two_thread_struct;



void thread_num_zero(Peterson_two_thread_struct *ptt)
{
    ptt->flag[0] = TRUE;
    ptt->turn = 1;
    __sync_synchronize();
    while (ptt->flag[1] && ptt->turn == 1)
    {
        // Wait
    }
    
    // Critical section
    for (int i = 0; i < 100; i++) {
        ptt->shared_value++;
        printf("[0] shared_value = %i\n", ptt->shared_value);
    }
    
    // End of critical section
    ptt->flag[0] = FALSE;
}

void thread_num_one(Peterson_two_thread_struct *ptt)
{
    ptt->flag[1] = TRUE;
    ptt->turn = 0;
    __sync_synchronize();    
    while (ptt->flag[0] && ptt->turn == 0)
    {
        // Wait
    }
    
    // Critical section
    for (int i = 0; i < 100; i++) {
        ptt->shared_value++;
        printf("[1] shared_value = %i\n", ptt->shared_value);
    }
    
    // End of critical section
    ptt->flag[1] = FALSE;
}


int main(int argc, const char * argv[]) {
    
    pthread_t pthread_0, pthread_1;

    Peterson_two_thread_struct ptt_struct;
    ptt_struct.flag[0] = FALSE;
    ptt_struct.flag[1] = FALSE;
    ptt_struct.shared_value = 0;
    
    printf("START : shared_value = %i\n", ptt_struct.shared_value);
    
    int ret0 = pthread_create(&pthread_0, NULL, PTHREAD_FUNCTION(thread_num_zero), &ptt_struct);
    int ret1 = pthread_create(&pthread_1, NULL, PTHREAD_FUNCTION(thread_num_one), &ptt_struct);
    
    // If the system can't create thread (see manual)
    if(ret0 != 0 || ret1 != 0)
    {
        printf("Error\n");
        printf("Thread \"thread_num_zero\" error : %i \n", ret0);
        printf("Thread \"thread_num_one\" error : %i \n", ret1);
        return -1;
    }
    
    pthread_join(pthread_0, NULL);
    pthread_join(pthread_1, NULL);
    
    printf("END : shared_value = %i\n", ptt_struct.shared_value);
    
    return 0;
}
