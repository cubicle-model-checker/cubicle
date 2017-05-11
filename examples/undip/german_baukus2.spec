
# shared= exgntd [true,false]
#         curcmd [empty,reqs,reqe]

# process= chan1       [empty,reqs,reqe]
#          chan2       [empty,inv,gnts,gnte]
#          chan3       [empty,invack]
#          shrset    [true,false]
#          invset [true,false]
# 	 curptr [true,false]
# 	 cache [invalid,shared,exclusive]

shared= exgntd [true,false]
        curcmd [empty,reqs,reqe,inv,gnts,gnte,invack]

process= chan1       [empty,reqs,reqe,inv,gnts,gnte,invack]
         chan2       [empty,reqs,reqe,inv,gnts,gnte,invack]
         chan3       [empty,reqs,reqe,inv,gnts,gnte,invack]
         shrset    [true,false]
         invset [true,false]
	 curptr [true,false]
	 cache [invalid,shared,exclusive]



commands:

UPRED

from 2: cache[1]=exclusive & cache[2]=shared

with


# send_req_shared
LC      cache=invalid & chan1=empty & chan1'=reqs

# send_req_exclusive
LC      cache=invalid & chan1=empty & chan1'=reqe
LC      cache=shared & chan1=empty & chan1'=reqe

# recv_req_shared
BDP     curcmd=empty & chan1=reqs & shrset=false
      & curcmd'=reqs & curptr'=true & invset'=false
      & chan1'=empty
      & [LR: p.invset'=true & p.shrset=true & p.curptr'=false]
      & [LR: p.invset'=false & p.shrset=false & p.curptr'=false]

BDP     curcmd=empty & chan1=reqs & shrset=true
      & curcmd'=reqs & curptr'=true & invset'=true
      & chan1'=empty
      & [LR: p.invset'=true & p.shrset=true & p.curptr'=false]
      & [LR: p.invset'=false & p.shrset=false & p.curptr'=false]


# recv_req_exclusive
BDP     curcmd=empty & chan1=reqs & shrset=false
      & curcmd'=reqe & curptr'=true & invset'=false
      & chan1'=empty
      & [LR: p.invset'=true & p.shrset=true & p.curptr'=false]
      & [LR: p.invset'=false & p.shrset=false & p.curptr'=false]
BDP     curcmd=empty & chan1=reqs & shrset=true
      & curcmd'=reqe & curptr'=true & invset'=true
      & chan1'=empty
      & [LR: p.invset'=true & p.shrset=true & p.curptr'=false]
      & [LR: p.invset'=false & p.shrset=false & p.curptr'=false]

# send_inv_1
LC      chan2=empty & invset=true & curcmd=reqe
      & chan2'=inv & invset'=false

# send_inv_2
LC      chan2=empty & invset=true & curcmd=reqs & exgntd=true
      & chan2'=inv & invset'=false


# send_invack
LC      chan2=inv & chan3=empty
      & chan2'=empty & chan3'=invack & cache'=invalid

# recv_invack
LC      chan3=invack & curcmd = reqs
      & exgntd'=false & chan3'=empty & shrset'=false
LC      chan3=invack & curcmd = reqe
      & exgntd'=false & chan3'=empty & shrset'=false

# send_gnt_shared
LC      curptr=true & curcmd=reqs & exgntd=false & chan2=empty
      & curcmd'=empty & chan2'=gnts & shrset'=true

# send_gnt_exclusive
BDP     curptr=true & curcmd=reqe & chan2=empty & shrset=false
      & curcmd'=empty & exgntd'=true & chan2'=gnte & shrset'=true
      & [LR: p.shrset=false]

# recv_gnt_shared
LC      chan2=gnts
      & cache'=shared & chan2'=empty

# recv_gnt_shared
LC      chan2=gnte
      & cache'=exclusive & chan2'=empty

initial 
        chan1= empty & chan2=empty & chan3=empty &
        invset=false & shrset=false & curcmd=empty &
        exgntd=false & cache=invalid
;

exit



