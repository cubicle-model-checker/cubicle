
shared= exclusive_granted [0..1]
        curr_command   [0..2]
        flag   [0..1]

process= channel1       [0..2]
         channel2       [0..3]
         channel3       [0..1]
         sharer_list    [0..1]
         invalidate_list [0..1]
	 curr_client [0..1]
	 cache [0..2]


commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: cache[1]=2 & cache[2]=1

with

# t1
LC      channel2=0 & curr_client=1 & flag=0 & curr_command=1 & exclusive_granted=0
      & sharer_list'=1 & curr_command'=0 & channel2'=1


# t2
BDP     channel2=0 & curr_client=1 & sharer_list=0 & flag=0 & curr_command=2 
      & sharer_list'=1 & curr_command'=0 & exclusive_granted'=1 & channel2'=2
      & [LR: p.sharer_list=0]

# t3
BDP     channel1=1 & flag=0 & curr_command=0 & sharer_list=0
      & curr_command'=1 & channel1'=0 & invalidate_list'=0
      & curr_client'=1 & flag'=1
      & [LR: p.curr_client'=0] 

# t3_
BDP     channel1=1 & flag=0 & curr_command=0 & sharer_list=1
      & curr_command'=1 & channel1'=0 & invalidate_list'=1
      & curr_client'=1 & flag'=1
      & [LR: p.curr_client'=0] 

# t4
BDP     channel1=2 & flag=0 & curr_command=0 & sharer_list=0
      & curr_command'=2 & channel1'=0 & invalidate_list'=0
      & curr_client'=1 & flag'=1
      & [LR: p.curr_client'=0] 

# t4_
BDP     channel1=2 & flag=0 & curr_command=0 & sharer_list=1
      & curr_command'=2 & channel1'=0 & invalidate_list'=1
      & curr_client'=1 & flag'=1
      & [LR: p.curr_client'=0] 

# t5
LC      flag=1 & invalidate_list'=0 & sharer_list=0

LC      flag=1 & invalidate_list'=1 & sharer_list=1


# t6
BDP     invalidate_list=0 & sharer_list=0 & flag=1 
      & flag'=0
      & [LR: p.invalidate_list=0 & p.sharer_list=0]
      & [LR: p.invalidate_list=1 & p.sharer_list=1]

# t6_
BDP     invalidate_list=1 & sharer_list=1 & flag=1 
      & flag'=0
      & [LR: p.invalidate_list=0 & p.sharer_list=0]
      & [LR: p.invalidate_list=1 & p.sharer_list=1]

# t7
LC      invalidate_list=1 & channel2=0 & flag=0 & curr_command=1 & exclusive_granted=1
      & channel2'=3 & invalidate_list'=0


# t8
LC      invalidate_list=1 & channel2=0 & flag=0 & curr_command = 2
      & channel2'=3 & invalidate_list'=0


# t9
LC      channel3=1 & flag=0 & curr_command=1
      & sharer_list'=0 & exclusive_granted'=0 & channel3'=0
# t9_
LC      channel3=1 & flag=0 & curr_command=2
      & sharer_list'=0 & exclusive_granted'=0 & channel3'=0


# t10
LC      cache=0 & channel1=0 & flag = 0 
      & channel1'=1

# t11_1
LC      cache=0 & channel1 =0 & flag=0 
      & channel1'=2

# t11_2
LC      cache=1 & channel1 =0 & flag=0 
      & channel1'=2

# t12
LC      channel2=3 & channel3=0 & flag = 0 
      & channel2'=0 & channel3'=1 & cache'=0

# t13
LC      channel2=1 & flag=0 
      & cache'=1 & channel2'=0

# t14
LC      channel2=2 & flag=0 
      & cache'=2 & channel2'=0


initial 
        exclusive_granted=0 & curr_command=0 & flag=0 & 
	channel1=0 & channel2=0 & channel3=0 & 
	sharer_list=0 & invalidate_list=0 & cache=0 
;

exit



