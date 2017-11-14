#!/bin/sh
for MA in `find basic_2 -name "*.ma"`; do
#for MA in `find -name "cpg*.ma" -or -name "cpx*.ma"`; do
   sed "s!$1!$2!g" ${MA} > ${MA}.new
   if [ ! -s ${MA}.new ] || diff ${MA} ${MA}.new > /dev/null; 
      then rm -f ${MA}.new; 
      else echo ${MA}; mv -f ${MA} ${MA}.old; mv -f ${MA}.new ${MA};
   fi
done

unset MA
