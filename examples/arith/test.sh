#!/bin/sh 

BASEDIR=$(dirname "$0")
CUBDIR="$BASEDIR/../.."
CUBICLE="$CUBDIR/cubicle.opt"
CALLING=$(pwd)
OCAMLRUNPARAM=b
TESTED="safe unsafe"

echo "Making..."
cd $CUBDIR && make && cd $CALLING

for testdir in $TESTED; 
	do
	for file in $(ls $BASEDIR/$testdir | grep .cub); 
	do
		echo "Testing $testdir/$file..."
		$CUBICLE -v $BASEDIR/$testdir/$file
	done
done

echo "done."
