#!/bin/sh
# script args: source_file target_file

use_clusters='no'
if [ ! -z "$USE_CLUSTERS" ]; then
  use_clusters=$USE_CLUSTERS
fi

# args: file snippet
# file will be modified in place
include_dot_snippet ()
{
  echo "Adding to $1 graphviz snippet $2 ..."
  sed -i "/digraph/r $2" $1
}

# args: stats file
# file will be modified in place
include_loc_stats ()
{
  echo "Adding to $1 KLOCs stats from $2 ..."
  tmp=`mktemp tmp.stats.XXXXXX`
  for l in `cat $2`; do
    module=$(basename $(echo $l | cut -d : -f 1))
    stat=$(echo $l | cut -d : -f 2)
    if [ "$stat" = "LOC" ]; then
      locs=$(echo $l | cut -d : -f 3)
      klocs=$(echo "scale=1; $locs / 1000" | bc)
      if [ "$klocs" = "0" ]; then klocs=".1"; fi
      printf '  %s [label="%s\\n%s klocs"];\n' $module $module $klocs >> $tmp
    fi
  done
  include_dot_snippet $1 $tmp
  rm $tmp
}

# args: file patch
apply_patch ()
{
  if [ -f "$2" ]; then
    echo "Applying to $1 patch $2 ..."
    patch $1 $2
  fi
}

cp $1 $2
include_loc_stats $2 .stats
apply_patch $2 STATS/deps.patch
include_dot_snippet $2 STATS/daemons.dot
if [ "$use_clusters" = "yes" ]; then
  include_dot_snippet $2 STATS/clusters.dot
fi

