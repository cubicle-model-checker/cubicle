process=  a [0..7]   # program counter
	  s [0..1]
	  w [0..1]
	  b [0..1]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: a[1]=7 & a[2]=7

with

LC	a=0 & a'=1 & b'=1

# rule 0: No other process with "s" set.
BDP    a=1 & a'=2 & b'=0 &
	& [LR: p.s=0]


# rule 1: set both "s" and "w" to 1.
LC	a=2 & a'=3 & s'=1 & w'=1


# rule 2: All other processes are either waiting, 
# or idle. Reset "w".
BDP    a=3 & a'=5 & w'=0  
	& [LR: p.w=1 | p.b=1]



# rule 3: There is another process not idle, 
# but not waiting yet. Reset s.
EXP	LR	a=3 & a'=4  & s'=0 & p.w=0 & p.b=0


# rule 4: There is another process with "s" set
# and not waiting. Set "s", reset "w".
# flag set to 2.
EXP	LR	a=4 & a'=5  & w'=0 & s'=1 
		& p.s=1 & p.w=0

# rule 5: None is waiting.
BDP    a=5 & a'=6  
	& [LR: p.w=0]


# rule 7: None to the left has "s" set.
BDP    a=6 & a'=7  
	& [L: p.s=0]

# rule 8: Get back to idle, reset "s".
LC	a=7 & a'=0 & s'=0 & b'=0 


# An initial configuration is one where all processes are idle with 
# both "s" and "w" set to 0.
initial a=0 & w=0 & s=0 & b=0

;

exit



