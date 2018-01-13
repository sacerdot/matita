for FILE in `find $1 -name "*.etc"`; do git mv $FILE ${FILE/%.etc/.ma} ; done
