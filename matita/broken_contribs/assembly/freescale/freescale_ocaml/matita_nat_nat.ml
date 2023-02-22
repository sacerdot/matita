type nat =
O
 | S of nat
;;

let nat_rec =
(function p -> (function f -> let rec aux = 
(function n -> 
(match n with 
   O -> p
 | S(n1) -> (f n1 (aux n1)))
) in aux))
;;

let nat_rect =
(function p -> (function f -> let rec aux = 
(function n -> 
(match n with 
   O -> p
 | S(n1) -> (f n1 (aux n1)))
) in aux))
;;

let pred =
(function n -> 
(match n with 
   O -> O
 | S(p) -> p)
)
;;

