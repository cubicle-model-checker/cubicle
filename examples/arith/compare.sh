#!/bin/bash
# Note : Require "GNU time"

BASEDIR=$(dirname "$0")
DIRTOTEST="$BASEDIR/.."
CUBDIR="$BASEDIR/../.."
CUBICLEOPT="$CUBDIR/cubicle.opt"
CUBICLE=cubicle
TIMECSV="$BASEDIR/time.csv"
NODECSV="$BASEDIR/node.csv"

# -----
# Arguments:
# 1 : Executable of Cubicle to test 
# 2 : File to test
# -----
tfunction () 
{
	echo "Testing $2 with $1"

	$1 -type-only $2
	if [ $? -ne 0 ];
	then
		echo "Error while typing/parsing."
		echo -n ";ParseError" >> $NODECSV
		echo -n ";ParseError" >> $TIMECSV	
	else
		COUT=$(timeout 2 /bin/time -f "time:%e" $1 $2 2>&1)
		# Time taken 
		CTIME=$(echo "$COUT" | grep "time")
		if [ -z "$CTIME" ];
		then
			echo "Timed out."
			echo -n ";TO" >> $NODECSV
			echo -n ";TO" >> $TIMECSV	
		else
			CTIME="${CTIME:5}"

			# Safe or unsafe ?
			CSOL=$(echo "$COUT" | grep "The system is")
			if [ -z "$CSOL" ];
			then
				CSOL=$(echo "$COUT" | grep "UNSAFE")
				#if [ -z "$CSOL" ];
				#then
				#	CSOL=$(echo "$COUT" | grep "trace")
				#fi
	
			else
				CSOL="${CSOL:14}"
			fi
			# Number of solver call
			CCALL=$(echo "$COUT" | grep "solver call" | grep -Eo "[0-9]*")

			# Number of visited nodes
			CNODE=$(echo "$COUT" | grep "visited nodes" | grep -Eo "[0-9]*")

			echo "Found $CSOL"
			echo -n ";$CNODE" >> $NODECSV
			echo -n ";$CTIME" >> $TIMECSV
		fi
	fi
}

echo "filename;arith;base" > $TIMECSV
echo "filename;arith;base" > $NODECSV

for filetotest in $(ls $DIRTOTEST | grep .cub)
do
	ALGNAME=$(basename $filetotest)
	echo -n "$ALGNAME" >> $TIMECSV
	echo -n "$ALGNAME" >> $NODECSV

	tfunction $CUBICLEOPT $DIRTOTEST/$filetotest
	tfunction $CUBICLE $DIRTOTEST/$filetotest

	echo >> $TIMECSV
	echo >> $NODECSV
done
