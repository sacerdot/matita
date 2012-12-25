F=`find $1 -name "*.ma" -or -name "*.txt"` 
while read A A A; do
   if grep -q "$A" $F; then true; else echo $A; fi
done
