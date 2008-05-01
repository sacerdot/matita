#!/bin/bash
set -e

MYSQL="mysql"
DBHOST="localhost"
DBNAME="matita"
DBUSER="helm"
DBPASS=""

TABLE_CREATOR="../../ocaml/metadata/table_creator/table_creator"

SQL="matita_db.sql"
STDLIB_DATA="matita_stdlib.sql.gz"

grant_sql="GRANT ALL PRIVILEGES ON $DBNAME.* TO $DBUSER@$DBHOST"
create_sql="CREATE DATABASE $DBNAME"
drop_sql="DROP DATABASE $DBNAME"

function appendsql()
{
  echo "$1" >> $SQL
}

echo "Step 0."
echo "  Dropping old databases, if any."
echo "  You can ignore errors output by this step"
echo "$drop_sql" | $MYSQL -f
echo "Step 1."
echo "  Creating database and users."
echo "# SQL statements to create Matita DB and users" > $SQL
appendsql "$create_sql;"
if [ -z "$DBPASS" ]; then
  appendsql "$grant_sql;"
else
  appendsql "$grant_sql IDENTIFIED BY '$DBPASS';"
fi
$MYSQL < $SQL
echo "Step 2."
echo "  Creating database structure."
echo "# SQL statements to create Matita DB structure" > $SQL
creator_args="table fill index"
for arg in $creator_args; do
  appendsql "`$TABLE_CREATOR $arg all`"
done
$MYSQL $DBNAME < $SQL
echo "Step 3."
echo "  Filling database with standard library metadata."
if [ -f "$STDLIB_DATA" ]; then
  gunzip -c "$STDLIB_DATA" | $MYSQL $DBNAME
else
  echo "  Standard library metadata file $STDLIB_DATA not found, skipping this step."
fi

