ALL_TABLES=`../table_creator/table_creator list all`

if [ -z "$1" ]; then
  echo "Dumps to stdout some tables of a given db on mowgli."
  echo "If no tables are given the dump will contain:"
  echo "  $ALL_TABLES"
  echo ""
  echo "usage: dump.sh dbname [tables...]"
  echo ""
  exit 1
fi
DB=$1
shift
if [ -z "$1" ]; then
  TABLES=$ALL_TABLES
else
  TABLES=$@
fi

mysqldump -e --add-drop-table -u helm -h mowgli.cs.unibo.it $DB $TABLES
