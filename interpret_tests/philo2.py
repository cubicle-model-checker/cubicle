import sys
import threading
import time
import random

n = 5 #int(sys.argv[1])
x = n
c = threading.Condition()
s = threading.Semaphore(n-1)

def yielde():
    time.sleep(random.uniform(0.1,0.5))
    #time.sleep(0)
    
def run(i):
    global c
    global x
    for k in range(3):
        s.acquire()

        # Get1_lock
        with c:
            # Get1:
            c.wait_for(lambda : x > 0)
            x -= 1
            # ReleaseGet1
            print(i,':get1')
        yielde()
        # Get2_lock
        with c:
            # Get2
            c.wait_for(lambda : x > 0)
            x -= 1
            # Release_Get2
            print(i,':get2')
            yielde()
            x += 2
            c.notify_all()
            print(i,':release')
        yielde()
        s.release()

P = [ threading.Thread(target=run, args=(i,)) for i in range(n)]
for i in range(n):
        P[i].start()

for i in range(n):
    P[i].join()

print('end')
