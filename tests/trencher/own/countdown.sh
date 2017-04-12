#!/bin/sh

nb=$1

echo "# Memory layout:
# 0 — x
# 1 — y

thread t1
initial q0
final qf
transition q0 q<  check < ri $nb
transition q< q1  write ri 0
transition q1 q0  local ri + ri 1
transition q0 q=  check == ri $nb
transition q= q0  local ri 0
transition q= q2  read r1 1
transition q2 qf  check == 0 r1
end

thread t2
initial q0
final qf
transition q0 q1  write 1 1
transition q1 q2  read r2 0
transition q2 q3  check == r2 1
transition q3 q4  read r2 0
transition q4 qf  check == r2 0
end
"
