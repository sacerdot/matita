#!/bin/sh
daemon="broker"
if [ "$1" = "--help" -o "$1" = "" ]; then
   echo "ctl.sh { start | stop | --help }"
   exit 0
fi
if [ "$1" = "start" ]; then
   echo -n "Starting HBugs broker ... "
   ./$daemon &> run/$daemon.log &
   echo "done!"
elif [ "$1" = "stop" ]; then
   echo -n "Stopping HBugs broker ... "
   killall -9 $daemon
   echo "done!"
fi
