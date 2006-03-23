#!/bin/bash

#configuration
TODAY=`date +%Y%m%d`
YESTERDAY=`date -d yesterday +%Y%m%d`
TMPDIRNAME=$HOME/__${TODAY}_crontab
TMPDIRNAMEOLD=$HOME/__${YESTERDAY}_crontab
SVNROOT="svn+ssh://mowgli.cs.unibo.it/local/svn/helm/trunk/"
SHELLTIME2CENTSPHP=scripts/shell_time2cents.php
SHELLADDERPHP=scripts/shell_adder.php
COMMONPHP=scripts/public_html/common.php
MYSQL="mysql -u helm -h mowgli.cs.unibo.it matita"
SQLQMARK="select distinct mark from bench where mark like '"
SQLQORD="' order by mark;"
SQLQTIME="select SUM(timeuser) from bench where mark = \""
SQLQGRMARK="\" group by mark;"
SQLQFAIL="select count(distinct test) from bench where mark = \""
SQLQFAIL1="select distinct test from bench where mark = \""
SQLQFAIL2="\" and result = 'fail';"
URL="http://mowgli.cs.unibo.it/~tassi/bench.php"

#initialization
OLD=$PWD
mkdir -p $TMPDIRNAME
rm -rf $TMPDIRNAMEOLD
cd $TMPDIRNAME
rm -rf helm
svn co ${SVNROOT}helm/software/matita/scripts/ > LOG.svn 2>&1

#run tests
scripts/profile_svn.sh 2> LOG

MARK=`echo $SQLQMARK$TODAY%$SQLQORD | $MYSQL | tail -n 1`
LASTMARK=`echo $SQLQMARK$YESTERDAY%$SQLQORD | $MYSQL | tail -n 1`

if [ -z "$MARK" ]; then
  echo "No benchmark records for $TODAY"
  exit 1
fi

if [ -z "$LASTMARK" ]; then
  echo "No benchmark records for $YESTERDAY"
  exit 1
fi

#check for slowdown
CUR_TIME=`echo $SQLQTIME$MARK$SQLQGRMARK | $MYSQL`
OLD_TIME=`echo $SQLQTIME$LASTMARK$SQLQGRMARK | $MYSQL`

if [ -z "$CUR_TIME" -o -z "$OLD_TIME"]; then
    cat <<EOT

    Unable to calculate total time amounts:
    
      $SQLQTIME$MARK$SQLQGRMARK 
      
    or

      $SQLQTIME$LASTMARK$SQLQGRMARK
      
    gave an empty result
    
EOT
fi

((DELTA=$CUR_TIME-$OLD_TIME))
if [ $DELTA -lt 0 ]; then
  PERC=0
else
  PREC=`scripts/functions.lua proportion $DELTA x $OLD_CENTS 100`
fi
if [ $PERC -ge 5 ]; then
  cat <<EOT
  
  PERFORMANCE LOSS DETECTED (MARK $MARK vs MARK $LASTMARK)
  
  Is `scripts/functions.lua t2s $CUR_TIME` 
  
  Was `scripts/functions.lua t2s $OLD_TIME`
  
  For details: $URL
EOT
fi

#check for more broken tests
CUR_FAIL=`echo $SQLQFAIL$MARK$SQLQFAIL2 | $MYSQL`
OLD_FAIL=`echo $SQLQFAIL$LASTMARK$SQLQFAIL2 | $MYSQL`

if [ $CUR_FAIL -gt $OLD_FAIL ]; then
  cat <<EOT

  MORE BROKEN TESTS DETECTED (MARK $MARK vs MARK $LASTMARK)
  
  Now broken:
`echo $SQLQFAIL1$MARK$SQLQFAIL2 | $MYSQL`

  Were broken:
`echo $SQLQFAIL1$LASTMARK$SQLQFAIL2 | $MYSQL`
  
  For details: $URL
EOT

fi

cd $OLD
#rm -rf $TMPDIRNAME

