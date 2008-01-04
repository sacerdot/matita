set "baseuri" "cic:/matita/tests/interactive/test6/".

whelp instance 
  \lambda A:Set.
  \lambda f:A \to A \to A.
  \forall x,y,z:A.
   f x (f y z) = f (f x y) z.
