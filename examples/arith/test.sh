#!/bin/sh 

BASEDIR=$(dirname "$0")
CUBDIR="$BASEDIR/../.."
CUBICLE="$CUBDIR/cubicle.opt"
CALLING=$(pwd)
OCAMLRUNPARAM=b

echo "Making..."
cd $CUBDIR && make && cd $CALLING

for file in $(ls $BASEDIR | grep .cub); 
do
	echo "Testing $file..."
	$CUBICLE -v -dot 4 $file
done

echo "done."
