#!/bin/bash

#configuration
MARK=`date +%Y%m%d%H%M`
TMPDIRNAME=__${MARK}_compilation
SVNROOT="svn+ssh://mowgli.cs.unibo.it/local/svn/helm/trunk/"
MYSQL="mysql -u helm -h mowgli.cs.unibo.it matita"
SVNLOG=LOG.svn

#helpers
function testit {
  LOGTOOPT=/dev/null
  LOGTOBYTE=/dev/null
  export BENCH_EXTRA_TEXT="$MARK $@"
  make tests.opt 
  #make tests 
}

function compile {
  LOCALOLD=$PWD
  cd $1
  autoconf 1>/dev/null
  ./configure 1>/dev/null
  make all opt 1>/dev/null
  cd $LOCALOLD
}

function run_tests {
  LOCALOLD=$PWD
  cd $1
  ./matitaclean all
  #export OCAMLRUNPARAM='o=100000'
  #testit "gc-off"
  export OCAMLRUNPARAM=''
  testit "gc-on"
  cd $LOCALOLD
}

#initialization
OLD=$PWD
rm -rf $TMPDIRNAME
mkdir $TMPDIRNAME
mkdir $TMPDIRNAME.HOME
cd $TMPDIRNAME

#svn checkout
svn co -N $SVNROOT > $SVNLOG 2>&1
cd trunk 
svn update -N helm >> $SVNLOG 2>&1
cd helm
svn update -N software >> $SVNLOG 2>&1
cd software
svn update $SVNOPTIONS components >> $SVNLOG 2>&1
svn update $SVNOPTIONS matita >> $SVNLOG 2>&1
cd ..
cd ..
cd ..
ln -s trunk/helm .

#compile
export HOME="`pwd`/../$TMPDIRNAME.HOME"
export USER="bench"
compile $PWD/helm/software/

#run
run_tests $PWD/helm/software/matita > LOG 2>LOG.run_tests.err

#insert the db
cat LOG | grep "\(OK\|FAIL\)" | grep "\(gc-on\|gc-off\)" | grep -v "bad_tests" | grep "^matitac" | grep -v "interactive" |\
  lua5.1 $PWD/helm/software/matita/scripts/functions.lua log2sql - > INSERT.sql
cat INSERT.sql | $MYSQL

#save the revision
SVNREVISION=`svn info $PWD/helm/software/ | grep "^Revision:" | cut -d : -f 2`
echo "INSERT INTO bench_svn VALUES ('$MARK','$SVNREVISION')" | $MYSQL
cd $OLD
#rm -rf $TMPDIRNAME

#eof
