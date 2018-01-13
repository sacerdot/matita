for FILE in `find $1 -name "*.ma"`; do git mv $FILE ${FILE/%.ma/.etc} ; done
