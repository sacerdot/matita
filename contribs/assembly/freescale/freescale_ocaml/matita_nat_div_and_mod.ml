let mod_aux =
let rec mod_aux = 
(function p -> (function m -> (function n -> 
(match (Matita_nat_compare.leb m n) with 
   Matita_datatypes_bool.True -> m
 | Matita_datatypes_bool.False -> 
(match p with 
   Matita_nat_nat.O -> m
 | Matita_nat_nat.S(q) -> (mod_aux q (Matita_nat_minus.minus m (Matita_nat_nat.S(n))) n))
)
))) in mod_aux
;;

let mod_ =
(function n -> (function m -> 
(match m with 
   Matita_nat_nat.O -> n
 | Matita_nat_nat.S(p) -> (mod_aux n n p))
))
;;

let div_aux =
let rec div_aux = 
(function p -> (function m -> (function n -> 
(match (Matita_nat_compare.leb m n) with 
   Matita_datatypes_bool.True -> Matita_nat_nat.O
 | Matita_datatypes_bool.False -> 
(match p with 
   Matita_nat_nat.O -> Matita_nat_nat.O
 | Matita_nat_nat.S(q) -> (Matita_nat_nat.S((div_aux q (Matita_nat_minus.minus m (Matita_nat_nat.S(n))) n))))
)
))) in div_aux
;;

let div =
(function n -> (function m -> 
(match m with 
   Matita_nat_nat.O -> (Matita_nat_nat.S(n))
 | Matita_nat_nat.S(p) -> (div_aux n n p))
))
;;

let div_mod_spec_rec =
(function n -> (function n1 -> (function n2 -> (function n3 -> (function f -> (f))))))
;;

let div_mod_spec_rect =
(function n -> (function n1 -> (function n2 -> (function n3 -> (function f -> (f))))))
;;

let n_divides_aux =
let rec n_divides_aux = 
(function p -> (function n -> (function m -> (function acc -> 
(match (mod_ n m) with 
   Matita_nat_nat.O -> 
(match p with 
   Matita_nat_nat.O -> (Matita_datatypes_constructors.Pair(acc,n))
 | Matita_nat_nat.S(p) -> (n_divides_aux p (div n m) m (Matita_nat_nat.S(acc))))

 | Matita_nat_nat.S(a) -> (Matita_datatypes_constructors.Pair(acc,n)))
)))) in n_divides_aux
;;

let n_divides =
(function n -> (function m -> (n_divides_aux n n m Matita_nat_nat.O)))
;;

