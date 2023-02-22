let divides_b =
(function n -> (function m -> (Matita_nat_compare.eqb (Matita_nat_div_and_mod.mod_ m n) Matita_nat_nat.O)))
;;

let smallest_factor =
(function n -> 
(match n with 
   Matita_nat_nat.O -> Matita_nat_nat.O
 | Matita_nat_nat.S(p) -> 
(match p with 
   Matita_nat_nat.O -> (Matita_nat_nat.S(Matita_nat_nat.O))
 | Matita_nat_nat.S(q) -> (Matita_nat_minimization.min_aux q (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))) (function m -> (Matita_nat_compare.eqb (Matita_nat_div_and_mod.mod_ (Matita_nat_nat.S((Matita_nat_nat.S(q)))) m) Matita_nat_nat.O))))
)
)
;;

let primeb =
(function n -> 
(match n with 
   Matita_nat_nat.O -> Matita_datatypes_bool.False
 | Matita_nat_nat.S(p) -> 
(match p with 
   Matita_nat_nat.O -> Matita_datatypes_bool.False
 | Matita_nat_nat.S(q) -> (Matita_nat_compare.eqb (smallest_factor (Matita_nat_nat.S((Matita_nat_nat.S(q))))) (Matita_nat_nat.S((Matita_nat_nat.S(q))))))
)
)
;;

