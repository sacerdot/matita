set "baseuri" "cic:/matita/tests/interactive/test5/".

whelp instance 
  \lambda A:Set. 
  \lambda f: A \to A \to A.
  \forall x,y : A.
      f x y = f y x.
