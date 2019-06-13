#!/bin/sh
for SRC in `find ground_2 static_2 basic_2 apps_2 -name "*.ma" -or -name "*.tbl"`; do
   sed "/$1/s!$2!$3!g" ${SRC} > ${SRC}.new
   if [ ! -s ${SRC}.new ] || diff ${SRC} ${SRC}.new > /dev/null; 
      then rm -f ${SRC}.new; 
      else echo ${SRC}; mv -f ${SRC} ${SRC}.old; mv -f ${SRC}.new ${SRC};
   fi
done

unset SRC
