type bool =
True
 | False
;;

let bool_rec =
(function p -> (function p1 -> (function b -> 
(match b with 
   True -> p
 | False -> p1)
)))
;;

let bool_rect =
(function p -> (function p1 -> (function b -> 
(match b with 
   True -> p
 | False -> p1)
)))
;;

let notb =
(function b -> 
(match b with 
   True -> False
 | False -> True)
)
;;

let andb =
(function b1 -> (function b2 -> 
(match b1 with 
   True -> b2
 | False -> False)
))
;;

let orb =
(function b1 -> (function b2 -> 
(match b1 with 
   True -> True
 | False -> b2)
))
;;

