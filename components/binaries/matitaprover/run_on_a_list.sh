#!/bin/bash

if [ -z "$1" ] || [ -z "$2" ]; then
  echo usage: $0 timeout problem_list
  exit 1
fi
gcc TreeLimitedRun.c -o TreeLimitedRun
> log
for PROBLEM in `cat $2`; do
  echo running on $PROBLEM
  ./TreeLimitedRun -q0 $1 $(($1*2)) ./matitaprover.native --tptppath ~/TPTP-v3.1.1/ $PROBLEM \
    >> log 2>&1
  echo So far `grep 'SZS status Unsatisfiable' log|wc -l` solved
done
echo Solved:
grep 'SZS status Unsatisfiable' log | wc -l
echo Failed:
grep 'Timeout' log | wc -l
