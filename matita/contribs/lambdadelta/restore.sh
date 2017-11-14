#!/bin/sh
for MA in `find -name "*.ma"`; do
   if [ -s ${MA}.old ];
      then echo ${MA}; mv -f ${MA}.old ${MA};
   fi
done

unset MA
