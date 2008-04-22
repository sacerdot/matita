let eqb =
let rec eqb = 
(function n -> (function m -> 
(match n with 
   Matita_nat_nat.O -> 
(match m with 
   Matita_nat_nat.O -> Matita_datatypes_bool.True
 | Matita_nat_nat.S(q) -> Matita_datatypes_bool.False)

 | Matita_nat_nat.S(p) -> 
(match m with 
   Matita_nat_nat.O -> Matita_datatypes_bool.False
 | Matita_nat_nat.S(q) -> (eqb p q))
)
)) in eqb
;;

let leb =
let rec leb = 
(function n -> (function m -> 
(match n with 
   Matita_nat_nat.O -> Matita_datatypes_bool.True
 | Matita_nat_nat.S(p) -> 
(match m with 
   Matita_nat_nat.O -> Matita_datatypes_bool.False
 | Matita_nat_nat.S(q) -> (leb p q))
)
)) in leb
;;

let ltb =
(function n -> (function m -> (Matita_datatypes_bool.andb (leb n m) (Matita_datatypes_bool.notb (eqb n m)))))
;;

let nat_compare =
let rec nat_compare = 
(function n -> (function m -> 
(match n with 
   Matita_nat_nat.O -> 
(match m with 
   Matita_nat_nat.O -> Matita_datatypes_compare.EQ
 | Matita_nat_nat.S(q) -> Matita_datatypes_compare.LT)

 | Matita_nat_nat.S(p) -> 
(match m with 
   Matita_nat_nat.O -> Matita_datatypes_compare.GT
 | Matita_nat_nat.S(q) -> (nat_compare p q))
)
)) in nat_compare
;;

