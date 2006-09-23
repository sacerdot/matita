#!/bin/bash
set -x

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
SQLQMARK="select distinct mark from bench where mark like '%s%%' order by mark;"
SQLQTIME="select SUM(timeuser) from bench where mark = '%s' group by mark;"
SQLQFAILCOUNT="select count(distinct test) from bench where mark = '%s' and result = 'fail';"
SQLQFAIL="select distinct test from bench where mark = '%s' and result = 'fail';"
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

MARK=`printf "$SQLQMARK" "$TODAY" | $MYSQL | tail -n 1`
LASTMARK=`printf "$SQLQMARK" "$YESTERDAY" | $MYSQL | tail -n 1`

if [ -z "$MARK" ]; then
  echo "No benchmark records for $TODAY"
  exit 1
fi

if [ -z "$LASTMARK" ]; then
  echo "No benchmark records for $YESTERDAY"
  exit 1
fi

#check for slowdown
CUR_TIME=`printf "$SQLQTIME" "$MARK" | $MYSQL | tail -n 1`
OLD_TIME=`printf "$SQLQTIME" "$LASTMARK" | $MYSQL | tail -n 1`

if [ -z "$CUR_TIME" -o -z "$OLD_TIME" ]; then
    cat <<EOT

    Unable to calculate total time amounts:
    
      `printf "$SQLQTIME" "$MARK"`
      
    or

      `printf "$SQLQTIME" "$LASTMARK"`
      
    gave an empty result
    
EOT
fi

((DELTA= $CUR_TIME - $OLD_TIME))
if [ "$DELTA" -lt 0 ]; then
  PERC=0
else
  PREC=`lua5.1 scripts/functions.lua proportion $DELTA x $OLD_TIME 100`
fi
if [ "$PERC" -ge 5 ]; then
  cat <<EOT
  
  Performance loss detected (MARK $MARK vs MARK $LASTMARK)
  
  Is: `lua5.1 scripts/functions.lua t2s $CUR_TIME` 
  Was: `lua5.1 scripts/functions.lua t2s $OLD_TIME`
  
  For details: $URL
EOT
fi

#check for more broken tests
CUR_FAIL=`printf "$SQLQFAILCOUNT" "$MARK" | $MYSQL | tail -n 1`
OLD_FAIL=`printf "$SQLQFAILCOUNT" "$LASTMARK" | $MYSQL | tail -n 1`

if [ "$CUR_FAIL" -gt "$OLD_FAIL" ]; then
  cat <<EOT

  More broken tests detected (MARK $MARK vs MARK $LASTMARK)
  Is: $CUR_FAIL
  Was: $OLD_FAIL 
  
  Now broken:
`printf "$SQLQFAIL" "$MARK" | $MYSQL`

  Were broken:
`printf "$SQLQFAIL" "$LASTMARK" | $MYSQL`
  
  For details: $URL
EOT

fi

cd $OLD
#rm -rf $TMPDIRNAME

