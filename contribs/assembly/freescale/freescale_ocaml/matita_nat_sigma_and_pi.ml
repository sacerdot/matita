let sigma =
let rec sigma = 
(function n -> (function f -> (function m -> 
(match n with 
   Matita_nat_nat.O -> (f m)
 | Matita_nat_nat.S(p) -> (Matita_nat_plus.plus (f (Matita_nat_plus.plus (Matita_nat_nat.S(p)) m)) (sigma p f m)))
))) in sigma
;;

let pi =
let rec pi = 
(function n -> (function f -> (function m -> 
(match n with 
   Matita_nat_nat.O -> (f m)
 | Matita_nat_nat.S(p) -> (Matita_nat_times.times (f (Matita_nat_plus.plus (Matita_nat_nat.S(p)) m)) (pi p f m)))
))) in pi
;;

