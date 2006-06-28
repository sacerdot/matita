#!/bin/sh

if [ -z "$1" ]; then
  TODO=Unsatisfiable/[A-Z]*.ma
else
  TODO=`cat $1`
fi

mkdir -p logs

i=1
for X in $TODO; do
  echo -n "$X ... "
  LOGNAME=logs/log.`basename $X`
  ../../matitac.opt -nodb $X > $LOGNAME 2>&1
  RATING=`grep "Rating" $X | sed 's/v.*//' | sed 's/(\*//'`
  if [ `grep "Found a proof" $LOGNAME | wc -l` -gt 0 ]; then
    TIME=`grep "TIME NEEDED" $LOGNAME`
    echo OK $TIME $RATING $i
  else
    echo FAIL $RATING $i
  fi
  i=`expr $i + 1`
  gzip -f $LOGNAME
done
