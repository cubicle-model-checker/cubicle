process= a [1..4]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: a[1]=3 & a[2]=3

with

# t1
BDP     a=4 & a'=1 & [LR: p.a=3 & p.a'=2]


# t2
BDP     a=1 & a'=1 & [LR: p.a=2 & p.a'=4] & [LR: p.a=1 & p.a'=4]


# t3
BDP     a=2 & a'=3 & [LR: p.a=1 & p.a'=4] & [LR: p.a=2 & p.a'=4]

# t4
BDP     a=4 & a'=3 & [LR: p.a=1 & p.a'=4] & [LR: p.a=2 & p.a'=4] & [LR: p.a=3 & p.a'=4]

initial a=1

;

exit



