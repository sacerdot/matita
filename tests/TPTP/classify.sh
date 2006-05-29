#!/bin/bash

mkdir Open
mkdir Unknown
mkdir Satisfiable
mkdir Unsatisfiable

for X in [A-Z]*.ma; do
  echo $X
  STATUS=`grep "^(\* *Status *:" $X`
  if [ `echo $STATUS | grep Open | wc -l` -eq 1 ]; then
    mv $X Open/
  fi
  if [ `echo $STATUS | grep Unknown | wc -l` -eq 1 ]; then
    mv $X Unknown/
  fi
  if [ `echo $STATUS | grep Satisfiable | wc -l` -eq 1 ]; then
    mv $X Satisfiable/
  fi
  if [ `echo $STATUS | grep Unsatisfiable | wc -l` -eq 1 ]; then
    mv $X Unsatisfiable/
  fi
done
