for FILE in `find $1 -name "*.etc"`; do svn mv $FILE ${FILE/%.etc/.ma} ; done
