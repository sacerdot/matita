set "baseuri" "cic:/matita/LOGIC/CLE/defs".

(* ORDER RELATION BETWEEN POSITIONS AND CONTEXTS
*)

include "datatypes/Context.ma".

inductive CLE: Nat \to Context \to Prop \def
   | cle_zero: \forall Q. CLE zero Q
   | cle_succ: \forall Q,i. CLE i Q \to 
               \forall p1,p2,R. CLE (succ i) (abst Q p1 p2 R)
.

interpretation "order relation between positions and contexts" 
   'leq x y = (cic:/matita/LOGIC/CLE/defs/CLE.ind#xpointer(1/1) x y).
