let max =
let rec max = 
(function i -> (function f -> 
(match (f i) with 
   Matita_datatypes_bool.True -> i
 | Matita_datatypes_bool.False -> 
(match i with 
   Matita_nat_nat.O -> Matita_nat_nat.O
 | Matita_nat_nat.S(j) -> (max j f))
)
)) in max
;;

let min_aux =
let rec min_aux = 
(function off -> (function n -> (function f -> 
(match (f n) with 
   Matita_datatypes_bool.True -> n
 | Matita_datatypes_bool.False -> 
(match off with 
   Matita_nat_nat.O -> n
 | Matita_nat_nat.S(p) -> (min_aux p (Matita_nat_nat.S(n)) f))
)
))) in min_aux
;;

let min =
(function n -> (function f -> (min_aux n Matita_nat_nat.O f)))
;;

