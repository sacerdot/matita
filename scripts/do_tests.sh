#!/bin/bash

OK="\e[32mOK\e[0m"
FAIL="\e[31mFAIL\e[0m"

if [ "$1" = "-no-color" ]; then
  shift
  OK="OK"
  FAIL="FAIL"
fi
if [ "$1" = "-twice" ]; then
  shift
  TWICE=1
fi
if [ "$1" = "-keep-logs" ]; then
  shift
  KEEP=1
fi

COMPILER=$1
shift
CLEANCOMPILER=`echo $COMPILER | cut -d ' ' -f 1`
CLEANER=$1
shift
LOGFILE=$1
shift
EXPECTED=$1
shift
TODO="$@"

if [ -z "$COMPILER" -o -z "$CLEANER" -o -z "$LOGFILE" -o -z "$EXPECTED" -o -z "$TODO" ]; then
  echo
  echo "usage: "
  echo "  do_tests.sh [-no-color] [-twice] [-keep-logs] ./compiler ./cleaner logfile expected_result test.ma ..."
  echo
  echo "options:  "
  echo "  -no-color Do not use vt100 colors"
  echo "  -twice    Run each test twice but show only the second run times"
  echo "  -keep-logs Do not dele __* files"
  echo
  echo "If expected_result is OK the result will be OK if the test compiles."
  echo "Otherwise if expected_result is FAIL the result will be OK if the test"
  echo "does not compile and the generated output is equal to test.log."
  echo "The value of the DO_TESTS_EXTRA evironment variable"
  echo "will be appended to each line."
  exit 1
fi


export TIMEFORMAT="%2lR %2lU %2lS"
for T in $TODO; do
  TT=`echo $T | sed s?/?.?`.not_for_matita
  LOG=__log_$TT
  DIFF=__diff_$TT
  printf "$CLEANCOMPILER\t%-30s   " $T
  if [ "$TWICE" = "1" ]; then
    $CLEANER $T 1>/dev/null 2>/dev/null
    $COMPILER $T 1>/dev/null 2>/dev/null
  fi
  $CLEANER $T 1>/dev/null 2>/dev/null
  TIMES=`(time $COMPILER $T > $LOG 2>&1) 2>&1`
  RC=$?;
  cat $LOG >> $LOGFILE
  touch $DIFF
  if [ $EXPECTED = "FAIL" ]; then
   if [ $RC = 0 ]; then
     echo "The test was successful but it should have failed!" > $DIFF
     RC=1;
   else
     diff $LOG `basename $T .ma`.log > $DIFF
     RC=$?
   fi
  fi
  if [ $RC = 0 ]; then
    printf "$OK\t$TIMES\t$DO_TESTS_EXTRA\n"
  else
    printf "$FAIL\t$TIMES\t$DO_TESTS_EXTRA\n";
    cat $DIFF
  fi
  if [ "$KEEP" != "1" ]; then
    rm -f $LOG
    rm -f $DIFF
  fi
  exit $RC
done
