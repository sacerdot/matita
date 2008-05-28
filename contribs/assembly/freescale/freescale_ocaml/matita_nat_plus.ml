let plus =
let rec plus = 
(function n -> (function m -> 
(match n with 
   Matita_nat_nat.O -> m
 | Matita_nat_nat.S(p) -> (Matita_nat_nat.S((plus p m))))
)) in plus
;;

