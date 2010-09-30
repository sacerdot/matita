#!/bin/sh

# sync metadata from a source database (usually "mowgli") to a target one
# (usually "matita")
# Created:        Fri, 13 May 2005 13:50:16 +0200 zacchiro
# Last-Modified:  Fri, 13 May 2005 13:50:16 +0200 zacchiro

SOURCE_DB="mowgli"
TARGET_DB="matita"
MYSQL_FLAGS="-u helm -h localhost"

MYSQL="mysql $MYSQL_FLAGS -f"
MYSQLDUMP="mysqldump $MYSQL_FLAGS"
MYSQLRESTORE="mysqlrestore $MYSQL_FLAGS"
TABLES=`./table_creator list all`
DUMP="${SOURCE_DB}_dump.gz"

echo "Dumping source db $SOURCE_DB ..."
$MYSQLDUMP $SOURCE_DB $TABLES | gzip -c > $DUMP
echo "Destroying old tables in target db $TARGET_DB ..."
./table_destructor table all | $MYSQL $TARGET_DB
echo "Creating table structure in target db $TARGET_DB ..."
echo "Filling target db $TARGET_DB ..."
zcat $DUMP | $MYSQL $TARGET_DB
./table_creator index all | $MYSQL $TARGET_DB
rm $DUMP
echo "Done."

