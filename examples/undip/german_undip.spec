
shared= exclusivegranted [true,false]
        currentcommand   [empty,grantshared,grantexclusive]
process= pc             [invalid,shared,exclusive]
         currentclient  [false,true]
         sharedlist     [false,true]
         invalidatelist [false,true]

	 channelone [empty,requestshared,requestexclusive]
	 channeltwo [empty,grantshared,grantexclusive,invalidate]
	 channelthree [empty,invalidateack]

commands:

UPRED

# A bad configuration is where at least two 
# processes are at their critical section.
from 2: pc[1]=exclusive & pc[2]=exclusive

with

#home0
#r1
LC	currentcommand=requestshared & exclusivegranted=false
      & channeltwo=empty & currentclient=true
      & currentcommand'=empty & sharedlist'=true 
      & channeltwo'=grantshared

#home1
#r2
BDP    currentcommand=requestexclusive & channeltwo=empty
#       & sharedlist=false 
       & currentclient=true
       & currentcommand'=empty & sharedlist'=true
       & exclusivegranted'=true & channeltwo'=grantexclusive
       & [LR: p.sharedlist=false]



#home2
#BDP    currentcommand=empty & channelone noq empty
#       & currentcommand'=theoneofchannelone & channelone'=empty
#       & invalidatelist'=theoneofsharedlist & currentclient'=true
#       & [LR: invalidatelist'=true & sharedlist=true
#             & currentclient'=false]
#       & [LR: invalidatelist'=false & sharedlist=false
#             & currentclient'=false]



#home2: channelone=requestshared, sharedlist=false
#r3
BDP    currentcommand=empty & channelone=requestshared
       & currentcommand'=requestshared & channelone'=empty
       & invalidatelist'=false & currentclient'=true
       & [LR: p.invalidatelist'=true & p.sharedlist=true
             & p.currentclient'=false]
       & [LR: p.invalidatelist'=false & p.sharedlist=false
             & p.currentclient'=false]

#home2: channelone=requestexclusive, sharedlist=false
#r4
BDP    currentcommand=empty & channelone=requestexclusive
       & currentcommand'=requestexclusive & channelone'=empty
       & invalidatelist'=false & currentclient'=true
       & [LR: p.invalidatelist'=true & p.sharedlist=true
             & p.currentclient'=false]
       & [LR: p.invalidatelist'=false & p.sharedlist=false
             & p.currentclient'=false]



#home2: channelone=requestshared, sharedlist=true
#r5
BDP    currentcommand=empty & channelone=requestshared
       & currentcommand'=requestshared & channelone'=empty
       & invalidatelist'=true & currentclient'=true
       & [LR: p.invalidatelist'=true & p.sharedlist=true
             & p.currentclient'=false]
       & [LR: p.invalidatelist'=false & p.sharedlist=false
             & p.currentclient'=false]

#home2: channelone=requestexclusive, sharedlist=true
#r6
BDP    currentcommand=empty & channelone=requestexclusive
       & currentcommand'=requestexclusive & channelone'=empty
       & invalidatelist'=true & currentclient'=true
       & [LR: p.invalidatelist'=true & p.sharedlist=true
             & p.currentclient'=false]
       & [LR: p.invalidatelist'=false & p.sharedlist=false
             & p.currentclient'=false]




#home3
#r7
LC     currentcommand=requestshared & exclusivegranted=true
       & invalidatelist=true & channeltwo=empty
       & invalidatelist'=false & channeltwo'=invalidate


#home4
#r8
LC     currentcommand=requestexclusive 
       & invalidatelist=true   & channeltwo=empty
       & invalidatelist'=false & channeltwo'=invalidate


#home5 grantshared,grantexclusive, invalidate
#LC     currentcommand not empty & channelthree=invalidatevack
#       & sharedlist'=false & exclusivegranted'=false
#       & channelythree'=empty

#home5 grantshared
#r9
LC     currentcommand=grantshared
       & channelthree=invalidateack
       & sharedlist'=false & exclusivegranted'=false
       & channelthree'=empty

#home5 grantexclusive
#r10
LC     currentcommand=grantexclusive
       & channelthree=invalidateack
       & sharedlist'=false & exclusivegranted'=false
       & channelthree'=empty



#client1
#r11
LC     pc=invalid 
       & channelone=empty
       & channelone'=requestshared

#client 2
#r12
LC     pc=invalid 
       & channelone=empty
       & channelone'=requestexclusive

#client3
#r13
LC    pc=shared
      & channelone=empty
      & channelone'=requestexclusive

#client4
#r14
LC    pc'=invalid
      & channeltwo=invalidate & channelthree=empty
      & channeltwo'=empty & channelthree'=invalidateack

#client5
#r15
LC    pc'=shared 
      & channeltwo=grantshared
      & channeltwo'=empty

#client6
#r16
LC    pc'=exclusive 
      & channeltwo=grantexclusive
      & channeltwo'=empty




initial     pc=invalid 
      & channelone=empty   & channeltwo=empty   
      & channelthree=empty & currentclient=false 
      & sharedlist=false & invalidatelist=false
      & exclusivegranted=false & currentclient=false

;

exit



