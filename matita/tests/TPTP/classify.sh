#!/bin/bash

mkdir -p Open
mkdir -p Unknown
mkdir -p Satisfiable
mkdir -p Unsatisfiable

for X in [A-Z]*.ma; do
  echo -n classifying $X ...
  STATUS=`grep "^(\* *Status *:" $X`
  if [ `echo $STATUS | grep Open | wc -l` -eq 1 ]; then
    mv $X Open/
    echo Open
  fi
  if [ `echo $STATUS | grep Unknown | wc -l` -eq 1 ]; then
    mv $X Unknown/
    echo Unknown
  fi
  if [ `echo $STATUS | grep Satisfiable | wc -l` -eq 1 ]; then
    mv $X Satisfiable/
    echo Satisfiable
  fi
  if [ `echo $STATUS | grep Unsatisfiable | wc -l` -eq 1 ]; then
    mv $X Unsatisfiable/
    echo Unsatisfiable
  fi
done
