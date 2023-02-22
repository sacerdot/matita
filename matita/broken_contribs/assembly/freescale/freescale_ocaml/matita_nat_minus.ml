let minus =
let rec minus = 
(function n -> (function m -> 
(match n with 
   Matita_nat_nat.O -> Matita_nat_nat.O
 | Matita_nat_nat.S(p) -> 
(match m with 
   Matita_nat_nat.O -> (Matita_nat_nat.S(p))
 | Matita_nat_nat.S(q) -> (minus p q))
)
)) in minus
;;

