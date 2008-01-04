set "baseuri" "cic:/matita/tests/interactive/test7/".

whelp instance 
  \lambda A:Set.
  \lambda r:A \to A \to Prop.
  \forall x:A.
   r x x.
