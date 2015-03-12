process= a [1..5]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: a[1]=1 & a[2]=1

with

# t1
LC	a=3 & a'=1

# t2
BDP	a=5 & a'=4 & [LR: p.a=3 & p.a'=4] & [LR: p.a=1 & p.a'=2]


# t3
BDP	a=4 & a'=3 & [LR: p.a'=5]

# t4
BDP	a=2 & a'=3 & [LR: p.a'=5]

# t5
BDP	a=5 & a'=3 & [LR: p.a'=5]


initial a=5

;

exit



