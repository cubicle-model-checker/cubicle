#/bin/sh

nb=$1 # script takes a positive integer as argument 

echo "forbidden
ASSERT ASSERT

data
  x = * : [0:1]
  y = * : [0:1]
  a = * : [0:$(($nb-1))]
  b = * : [0:$(($nb-1))]

process
registers
  \$r = * : [0:$(($nb-1))]
text
  L0: write: x := 1;
      read: \$r := a;
      either {"

for i in `seq 1 $(($nb-1))`
do
echo "        if \$r = $((${i}-1)) then
          write: a := $((${i} % $nb))
      or"
done

echo "        if \$r = $(($nb-1)) then
          write: a := 0
      };"

echo "      read: \$r := y;
      if \$r = 0 then
        goto ASSERT;
ASSERT:
      nop

process
registers
  \$r = * : [0:$(($nb-1))]
text
  L0: write: y := 1;
      read: \$r := b;
      either {"

for i in `seq 1 $(($nb-1))`
do
echo "        if \$r = $((${i}-1)) then
          write: b := $((${i} % $nb))
      or"
done

echo "        if \$r = $(($nb-1)) then
          write: b := 0
      };"

echo "      read: \$r := x;
      if \$r = 0 then
        goto ASSERT;
ASSERT:
      nop"

