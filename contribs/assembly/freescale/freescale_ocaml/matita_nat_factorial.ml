let fact =
let rec fact = 
(function n -> 
(match n with 
   Matita_nat_nat.O -> (Matita_nat_nat.S(Matita_nat_nat.O))
 | Matita_nat_nat.S(m) -> (Matita_nat_times.times (Matita_nat_nat.S(m)) (fact m)))
) in fact
;;

