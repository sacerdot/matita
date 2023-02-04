#!/bin/sh

prover=y

MATITAC=../../matitac.opt
#MATITAC=../../matitac
MATITAPROVER=../../matitaprover.opt
TPTPPATH=/home/tassi/TPTP-v3.1.1/

if [ -z "$1" ]; then
  if [ $prover = 'y' ]; then
    TODO=`cat elenco_unsatisfiable.txt`	  
  else
    TODO=Unsatisfiable/[A-Z]*.ma
  fi
else
  TODO=`cat $1`
fi

mkdir -p logs

i=1
for X in $TODO; do
  echo -n "$X ... "
  LOGNAME=logs/log.`basename $X`
  if [ $prover = 'y' ]; then
    $MATITAPROVER -tptppath $TPTPPATH $X > $LOGNAME 2>&1
  else
    $MATITAC -nodb $X > $LOGNAME 2>&1
  fi
  if [ $prover = 'y' ]; then
    BASE=`echo $X | cut -c 1-3`	  
    RATING=`grep "Rating" $TPTPPATH/Problems/$BASE/$X | sed 's/v.*//' | sed 's/%//'`	  
  else
    RATING=`grep "Rating" $X | sed 's/v.*//' | sed 's/(\*//'`
  fi
  if [ `grep "Found a proof" $LOGNAME | wc -l` -gt 0 ]; then
    TIME=`grep "TIME" $LOGNAME`
    MAXWEIGHT=`grep "max weight:" $LOGNAME`
    echo OK $TIME $RATING $MAXWEIGHT $i
  else
    echo FAIL $RATING $i
  fi
  i=`expr $i + 1`
  gzip -f $LOGNAME
done
