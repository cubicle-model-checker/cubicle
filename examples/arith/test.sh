#!/bin/sh 

BASEDIR=$(dirname "$0")
CUBICLE="$BASEDIR/../../cubicle.opt"

for file in $(ls $BASEDIR | grep .cub); 
do
	$CUBICLE -type-only $file	
done
