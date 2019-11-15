#!/bin/sh
for SRC in `find ground_2 static_2 basic_2 apps_2 -name "*.ma"`; do
  if [ ! -e ${SRC//$1/$2} ];
    then echo ${SRC//$1/$2}; git mv $SRC ${SRC//$1/$2};
  fi
done

unset SRC
