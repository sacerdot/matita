#!/bin/sh

input=$1

for X in `cat elenco_CASC.txt`; do
  grep ^$X $input 
done
