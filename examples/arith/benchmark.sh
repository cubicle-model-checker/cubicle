#!/bin/sh
# Note : Require "GNU time" in /bin/

# Usage : Simply run ./benchmark.sh.
# If you also wish to run default cubicle (cubicle in path), use any arg.

# TODO 
# Should probably take argument to specify timeout

BASEDIR=$(dirname "$0")
DIRTOTEST="$BASEDIR/.."
CUBDIR="$BASEDIR/../.."
CUBICLEOPT="$CUBDIR/cubicle.opt"
CUBICLE=cubicle
TIMECSV="$BASEDIR/time.csv"
NODECSV="$BASEDIR/node.csv"
CALLCSV="$BASEDIR/call.csv"
DUMP="$BASEDIR/benchmark_dump"

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
    for csv in $NODECSV $TIMECSV $CALLCSV do
      echo -n ";ParseError" >> $csv
    done
	else
		COUT=$(timeout 1m /bin/time -f "time:%e" $1 $2 2>&1)
		# Time taken 
		CTIME=$(echo "$COUT" | grep "time")
		if [ -z "$CTIME" ];
		then
			echo "Timed out."
      for csv in $NODECSV $TIMECSV $CALLCSV do
        echo -n ";TO" >> $csv
      done
		else
			CTIME="${CTIME:5}"

			# Safe or unsafe ?
			CSOL=$(echo "$COUT" | grep "The system is")
			if [ -z "$CSOL" ];
			then
				CSOL=$(echo "$COUT" | grep "UNSAFE")
				if [ -z "$CSOL" ];
				then
					CSOL=$(echo "$COUT" | grep "trace")
				fi
			else
				CSOL="${CSOL:14}"
			fi

			# Number of solver call
			CCALL=$(echo "$COUT" | grep "solver calls" | grep -Eo "[0-9]*")

			# Number of visited nodes
			CNODE=$(echo "$COUT" | grep "visited nodes" | grep -Eo "[0-9]*")

			echo "Found $CSOL"
      echo -n ";$CNODE" >> $NODECSV
			echo -n ";$CTIME" >> $TIMECSV
      echo -n ";$CCALL"  >> $CALLCSV
      echo "$COUT" >> $DUMP
		fi
	fi
}

echo > $DUMP

for csv in $NODECSV $TIMECSV $CALLCSV
do
  if [ -z $1 ]; then
    echo "filename;arith;base" > $csv
  else
    echo "filename;arith" > $csv
  fi;
done

for filetotest in $(ls $DIRTOTEST | grep .cub)
do
	ALGNAME=$(basename $filetotest)
  for csv in $NODECSV $TIMECSV $CALLCSV
  do
    echo -n "$ALGNAME" >> $csv
  done

	tfunction $CUBICLEOPT $DIRTOTEST/$filetotest
  
  if [ ! -z $1]; then
    tfunction $CUBICLE $DIRTOTEST/$filetotest
  fi;

  for csv in $NODECSV $TIMECSV $CALLCSV
  do
    echo >> $csv
  done

done
