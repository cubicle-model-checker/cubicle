process= a [1..4]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: a[1]=3 & a[2]=3

with

# t1
BDP	a=4 & a'=1 & [LR: a=3 & a'=2]


# t2
BDP	a=1 & a'=1 & [LR: a=2 & a'=4] & [LR: a=1 & a'=4]


# t3
BDP	a=2 & a'=3 & [LR: a=2 & a'=4] & [LR: a=1 & a'=4]


# t4
BDP	a=4 & a'=3 & [LR: a=2 & a'=4] & [LR: a=1 & a'=4] & [LR: a=3 & a'=4] 


initial a=4

;

exit



