#!/bin/sh

nb=$1

echo "# Memory layout:
# 0 — x
# 1 — y
# 2 - a
# 3 - b

thread t0
initial q0
final qcs
transition q0 q1 write 1 0
transition q1 q2 read r 2"
last=2

for i in `seq 1 $nb`
do
echo "
transition  q$last  q1${i}  check == r $((${i}-1))
transition  q1${i}  q3      write $((${i} % $nb )) 2"
done
last=3

echo "
transition  q$last  qenter  read r 1
transition  qenter  qcs check == r 0
end

# Thread t1 is symmetric.
thread t1
initial q0
final qcs
transition q0 q1 write 1 1
transition q1 q2 read r 3"
last=2

for i in `seq 1 $nb`
do
echo "
transition  q$last  q1${i}  check == r $((${i}-1))
transition  q1${i}  q3      write $((${i} % $nb)) 3"
done
last=3

echo "
transition  q$last  qenter  read r 0
transition  qenter  qcs check == r 0
end
"
