#!/bin/sh
# Copyright (C) 2003:
#    Stefano Zacchiroli <zack@cs.unibo.it>
#    for the HELM Team http://helm.cs.unibo.it/
# 
#  This file is part of HELM, an Hypertextual, Electronic
#  Library of Mathematics, developed at the Computer Science
#  Department, University of Bologna, Italy.
# 
#  HELM is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
# 
#  HELM is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
# 
#  You should have received a copy of the GNU General Public License
#  along with HELM; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
#  MA  02111-1307, USA.
# 
#  For details, see the HELM World-Wide-Web page,
#  http://helm.cs.unibo.it/
if [ "$1" = "--help" -o "$1" = "" ]; then
   echo "sabba.sh { start | stop | --help }"
   exit 0
fi

./scripts/ls_tutors.ml |
while read line; do
   tutor=`echo $line | sed 's/\.ml//'`
   if [ "$1" = "stop" ]; then
      echo -n "Stopping HBugs tutor $tutor ... "
      killall -9 $tutor
      echo "done!"
   elif [ "$1" = "start" ]; then
      echo -n "Starting HBugs tutor $tutor ... "
      nice -n 19 ./$tutor &> run/$tutor.log &
      echo "done!"
   else
      echo "Uh? Try --help"
      exit 1
   fi
done
