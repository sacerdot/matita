#!/bin/bash
TODAY=`date +%Y%m%d`
YESTERDAY=`date -d yesterday +%Y%m%d`
TMPDIRNAME=$HOME/__${TODAY}_crontab
TMPDIRNAMEOLD=$HOME/__${YESTERDAY}_crontab
SVNROOT="svn+ssh://mowgli.cs.unibo.it/local/svn/helm/trunk/"
SHELLTIME2CENTSPHP=scripts/shell_time2cents.php
SHELLADDERPHP=scripts/shell_adder.php
COMMONPHP=scripts/public_html/common.php


OLD=$PWD
mkdir -p $TMPDIRNAME
rm -rf $TMPDIRNAMEOLD
cd $TMPDIRNAME
rm -rf helm
svn co ${SVNROOT}helm/matita/scripts/ > LOG.svn 2>&1
scripts/profile_svn.sh 2> LOG

MARK=`echo "select distinct mark from bench where mark like '$TODAY%' order by mark" | mysql -u helm matita | tail -n 1`
LASTMARK=`echo "select distinct mark from bench where mark like '$YESTERDAY%' order by mark" | mysql -u helm matita | tail -n 1`

if [ -z "$MARK" ]; then
  echo "No benchmark records for $TODAY"
  exit 1
fi

if [ -z "$LASTMARK" ]; then
  echo "No benchmark records for $YESTERDAY"
  exit 1
fi

CUR_TIME=`/usr/bin/php4 -c /etc/php4/apache/php.ini -f $SHELLADDERPHP -- $COMMONPHP "select SEC_TO_TIME(SUM(TIME_TO_SEC(time))) from bench where mark = \"$MARK\" group by mark;"`
OLD_TIME=`/usr/bin/php4 -c /etc/php4/apache/php.ini -f $SHELLADDERPHP -- $COMMONPHP  "select SEC_TO_TIME(SUM(TIME_TO_SEC(time))) from bench where mark = \"$LASTMARK\" group by mark;"`

CUR_CENTS=`/usr/bin/php4 -c /etc/php4/apache/php.ini -f $SHELLTIME2CENTSPHP -- $COMMONPHP $CUR_TIME`
OLD_CENTS=`/usr/bin/php4 -c /etc/php4/apache/php.ini -f $SHELLTIME2CENTSPHP -- $COMMONPHP $OLD_TIME`

((DELTA=$CUR_CENTS-$OLD_CENTS))
if [ $DELTA -lt 0 ]; then
  PERC=0
else
  ((PERC=100 * $DELTA))
  ((PERC=$PERC / $OLD_CENTS))
fi
if [ $PERC -ge 5 ]; then
  cat <<EOT
  REPORT FOR `date`
  http://mowgli.cs.unibo.it/~tassi/bench.php

  PERFORMANCE LOSS DETECTED (MARK $MARK vs MARK $LASTMARK)
  is $CUR_TIME sec 
  was $OLD_TIME sec

EOT
fi

CUR_FAIL=`/usr/bin/php4 -c /etc/php4/apache/php.ini -f $SHELLADDERPHP -- $COMMONPHP "select count(distinct test) from bench where mark = \"$MARK\" and result = 'fail';"`
OLD_FAIL=`/usr/bin/php4 -c /etc/php4/apache/php.ini -f $SHELLADDERPHP -- $COMMONPHP "select count(distinct test) from bench where mark = \"$LASTMARK\" and result = 'fail';"`

if [ $CUR_FAIL -gt $OLD_FAIL ]; then
  cat <<EOT
  REPORT FOR `date`
  http://mowgli.cs.unibo.it/~tassi/bench.php

  MORE BROKEN TESTS DETECTED (MARK $MARK vs MARK $LASTMARK)
  now broken:
  `echo "select distinct test from bench where mark = \"$MARK\" and result = 'fail';" | mysql -u helm -h mowgli.cs.unibo.it matita`
  were broken:
  `echo "select distinct test from bench where mark = \"$LASTMARK\" and result = 'fail';" | mysql -u helm -h mowgli.cs.unibo.it matita`
  
EOT

fi

cd $OLD
#rm -rf $TMPDIRNAME

