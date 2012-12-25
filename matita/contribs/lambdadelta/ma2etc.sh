for FILE in `find $1 -name "*.ma"`; do svn mv $FILE ${FILE/%.ma/.etc} ; done
