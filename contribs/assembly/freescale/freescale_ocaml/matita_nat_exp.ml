let exp =
let rec exp = 
(function n -> (function m -> 
(match m with 
   Matita_nat_nat.O -> (Matita_nat_nat.S(Matita_nat_nat.O))
 | Matita_nat_nat.S(p) -> (Matita_nat_times.times n (exp n p)))
)) in exp
;;

