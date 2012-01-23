
process= a [1..5]
	 b [0..1]
	 h [0..3]
	 c [0..oo]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: a[1]=2 & a[2]=2

with

# t1
LC	a=1 & b=0 & 1<=c & b'=1 & a'=2


# t2
LC	a=1 & b=1 & 1<=c & 1<=c'-c & -1<=c-c'  & a'=3


# t3
LC	a=2 & b=1 & c=0 & 1<=c-c' & -1<=c'-c & a'=4


# t4
LC	a=2 & b=1 & 1<=c & 1<=c-c' & -1<=c'-c & a'=4


# t5
LC	a=3 & h=0 & 1<=c & h'=1 & a'=5

# t6
LC	a=4 & h=0 & 1<=c & h'=2 & a'=1

# t7
LC	a=4 & h=1 & 1<=c & h'=3 & a'=1


# t8
LC	a=3 & h=2 & 1<=c & h'=3 & a'=5


# t9
LC	a=5 & h=3 & 1<=c & h'=0 & a'=2


initial a=1 & b=0 & h=0 & 1<=c

;

exit



