#!/bin/sh

if [ -z "$1" ]; then
  TODO=Unsatisfiable/[A-Z]*.ma
else
  TODO=`cat $1`
fi

mkdir -p logs

for X in $TODO; do
  echo -n "$X ... "
  LOGNAME=logs/log.`basename $X`
  ../../matitac.opt $X > $LOGNAME 2>&1
  if [ `grep "Found a proof" $LOGNAME | wc -l` -gt 0 ]; then
    TIME=`grep "TIME NEEDED" $LOGNAME`
    RATING=`grep "Rating" $X | sed 's/v.*//' | sed 's/(\*//'`
    echo OK $TIME $RATING
  else
    echo FAIL
  fi
done
