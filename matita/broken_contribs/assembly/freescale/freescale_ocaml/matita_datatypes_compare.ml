type compare =
LT
 | EQ
 | GT
;;

let compare_rec =
(function p -> (function p1 -> (function p2 -> (function c -> 
(match c with 
   LT -> p
 | EQ -> p1
 | GT -> p2)
))))
;;

let compare_rect =
(function p -> (function p1 -> (function p2 -> (function c -> 
(match c with 
   LT -> p
 | EQ -> p1
 | GT -> p2)
))))
;;

let compare_invert =
(function c -> 
(match c with 
   LT -> GT
 | EQ -> EQ
 | GT -> LT)
)
;;

