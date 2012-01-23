
shared= memory [0..oo]

process= cachedata [0..oo]
	 cachestate [invalid,shared,exclusive]


commands:

UPRED

from 2: cachestate[1]=exclusive & cachestate[2]=exclusive

with


# atomwb
LC      cachestate=exclusive & cachestate'=invalid

# atom_invalidate
LC      cachestate=invalid & cachestate'=invalid
LC      cachestate=shared & cachestate'=invalid


#atom_get1
BDP     cachestate=invalid & cachestate'=shared
      & [LR: p.cachestate=invalid]
      & [LR: p.cachestate=shared]
BDP     cachestate=shared & cachestate'=shared
      & [LR: p.cachestate=invalid]
      & [LR: p.cachestate=shared]

# atom_get2
EXP  LR cachestate=exclusive & cachestate'=shared & p.cachestate'=shared


# atom_getX_1
BDP     cachestate=invalid & cachestate'=exclusive
      & [LR: p.cachestate=invalid]
      & [LR: p.cachestate=shared]
BDP     cachestate=shared & cachestate'=exclusive
      & [LR: p.cachestate=invalid]
      & [LR: p.cachestate=shared]

# atom_getX_2
EXP  LR cachestate=exclusive & cachestate'=invalid & p.cachestate'=exclusive



initial 
        cachestate=invalid
;

exit



