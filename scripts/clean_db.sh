#!/bin/sh

TBL=`echo show tables | mysql matita -u helm | grep -v _`
for X in $TBL; do
  echo cleaning $X
  echo "delete from $X where source like 'cic:/matita/%'" | mysql matita -u helm
done
