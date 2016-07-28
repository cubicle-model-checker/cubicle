#!/bin/bash
# Iterating on each file which name is included in the
# "files.bench" file and execute two commands. A basic one and
# one with an option

out_file=$1
option=$2
time=1m

rm $out_file
touch $out_file

IFS=' '
while read -ra line; do
    filename="${line[0]}"
    brab="${line[1]}"
    fd="${line[2]}"
    bcmd="timeout $time ./cubicle.opt -brabfd $brab $fd examples/$filename\
          -quiet -profiling -res $out_file"
    ecmd=$bcmd" "$option
    echo $bcmd
    echo $ecmd
    $bcmd &> /dev/null
    $ecmd &> /dev/null
    echo "================================================================================" >> $out_file
done <files.bench
