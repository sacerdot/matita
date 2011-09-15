#!/bin/sh
for V in `cat Make`; do
   echo ${V}; sed "s/$1/$2/g" ${V} > ${V}.new
   if diff ${V} ${V}.new > /dev/null; 
      then rm -f ${V}.new; else mv -f ${V}.new ${V}; fi
done

unset V
