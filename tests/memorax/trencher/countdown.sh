#/bin/sh

nb=$1 # script takes a positive integer as argument 

echo "forbidden
CS CS

data
  x = * : [0:$nb]
  y = * : [0:1]

process
registers
  \$r = * : [0:1]
  \$ri = * : [0:$nb]
text
  L0: while \$ri < $nb do {
        write: x := \$ri;
        \$ri := \$ri + 1
      };
      either{
        read: \$r := y;
        if \$r = 0 then
          CS: nop
      or
        \$ri := 0;
        goto L0
      }

process
registers
  \$r = * : [0:$nb]
text
  write: y := 1;
  read: \$r := x;
  if \$r = 1 then {
    read: \$r := x;
    if \$r = 0 then
      CS: nop
  }
"
