#!/bin/sh
for SRC in `find -name "*.ma" -or -name "*.tbl"`; do
   if [ -s ${SRC}.old ];
      then echo ${SRC}; mv -f ${SRC}.old ${SRC};
   fi
done

unset SRC
