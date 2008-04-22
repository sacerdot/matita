let times =
let rec times = 
(function n -> (function m -> 
(match n with 
   Matita_nat_nat.O -> Matita_nat_nat.O
 | Matita_nat_nat.S(p) -> (Matita_nat_plus.plus m (times p m)))
)) in times
;;

