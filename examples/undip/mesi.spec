process= a [1..4]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: a[1]=4 & a[2]=4

with

# t1
LC      a=1 & a'=4


# t2
BDP	a=4 & a'=3 & [LR: p.a=1 & p.a'=3] & [LR: p.a=4 & p.a'=3] & [LR: p.a=2 & p.a'=2] & [LR: p.a=4 &  p.a'=3]
#check this 


# t3
BDP	a=3 & a'=1 & [LR: p.a'=2]


# t4
BDP	a=2 & a'=1 & [LR: p.a'=2]


initial a=2

;

exit



