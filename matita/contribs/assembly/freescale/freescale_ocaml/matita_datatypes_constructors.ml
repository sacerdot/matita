type void = unit (* empty type *)
;;

let void_rec =
(function v -> assert false)
;;

let void_rect =
(function v -> assert false)
;;

type unit =
Something
;;

let unit_rec =
(function p -> (function u -> 
(match u with 
   Something -> p)
))
;;

let unit_rect =
(function p -> (function u -> 
(match u with 
   Something -> p)
))
;;

type ('a,'b) prod =
Pair of 'a * 'b
;;

let prod_rec =
(function f -> (function p -> 
(match p with 
   Pair(t,t1) -> (f t t1))
))
;;

let prod_rect =
(function f -> (function p -> 
(match p with 
   Pair(t,t1) -> (f t t1))
))
;;

let fst =
(function p -> 
(match p with 
   Pair(a,b) -> a)
)
;;

let snd =
(function p -> 
(match p with 
   Pair(a,b) -> b)
)
;;

type ('a,'b) sum =
Inl of 'a
 | Inr of 'b
;;

let sum_rec =
(function f -> (function f1 -> (function s -> 
(match s with 
   Inl(t) -> (f t)
 | Inr(t) -> (f1 t))
)))
;;

let sum_rect =
(function f -> (function f1 -> (function s -> 
(match s with 
   Inl(t) -> (f t)
 | Inr(t) -> (f1 t))
)))
;;

type ('a) option =
None
 | Some of 'a
;;

let option_rec =
(function p -> (function f -> (function o -> 
(match o with 
   None -> p
 | Some(t) -> (f t))
)))
;;

let option_rect =
(function p -> (function f -> (function o -> 
(match o with 
   None -> p
 | Some(t) -> (f t))
)))
;;

