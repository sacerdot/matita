#!/bin/bash
MARK=`date +%Y%m%d%H%M`
TMPDIRNAME=__${MARK}_compilation
SVNROOT="svn+ssh://mowgli.cs.unibo.it/local/svn/helm/trunk/"

function testit {
  LOGTOOPT=/dev/null
  LOGTOBYTE=/dev/null
  export DO_TESTS_EXTRA="$MARK\t$@"
  make tests DO_TESTS_OPTS="-no-color -twice -keep-logs"
  make tests.opt DO_TESTS_OPTS="-no-color -twice -keep-logs"
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
  mkdir .matita
  export OCAMLRUNPARAM='o=1000000'
  testit "gc-off"
  export OCAMLRUNPARAM=''
  testit "gc-on"
  cd $LOCALOLD
}

OLD=$PWD
rm -rf $TMPDIRNAME
mkdir $TMPDIRNAME
mkdir $TMPDIRNAME.HOME
cd $TMPDIRNAME
SVNLOG=`pwd`/LOG.svn

#svn
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
compile $PWD/helm/software/

#run
run_tests $PWD/helm/software/matita > LOG 2>/dev/null

cat LOG | grep "\(OK\|FAIL\)" | grep "\(gc-on\|gc-off\)" | awk -f $PWD/helm/software/matita/scripts/insert.awk > INSERT.sql
cat INSERT.sql | mysql -u helm -h mowgli.cs.unibo.it matita
SVNREVISION=`cat $SVNLOG | grep revision | tail -n 1 | sed "s/.*revision \(\w\+\)./\1/"`
echo "INSERT INTO bench_svn VALUES ('$MARK','$SVNREVISION')" | mysql -u helm -h mowgli.cs.unibo.it matita
cd $OLD
#rm -rf $TMPDIRNAME
