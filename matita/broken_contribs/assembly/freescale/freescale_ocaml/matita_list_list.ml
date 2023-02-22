type ('a) list =
Nil
 | Cons of 'a * ('a) list
;;

let list_rec =
(function p -> (function f -> let rec aux = 
(function l -> 
(match l with 
   Nil -> p
 | Cons(t,l1) -> (f t l1 (aux l1)))
) in aux))
;;

let list_rect =
(function p -> (function f -> let rec aux = 
(function l -> 
(match l with 
   Nil -> p
 | Cons(t,l1) -> (f t l1 (aux l1)))
) in aux))
;;

let id_list =
let rec id_list = 
(function l -> 
(match l with 
   Nil -> (Nil)
 | Cons(hd,tl) -> (Cons(hd,(id_list tl))))
) in id_list
;;

let append =
let rec append = 
(function l1 -> (function l2 -> 
(match l1 with 
   Nil -> l2
 | Cons(hd,tl) -> (Cons(hd,(append tl l2))))
)) in append
;;

let tail =
(function l -> 
(match l with 
   Nil -> (Nil)
 | Cons(hd,tl) -> tl)
)
;;

let x1 =
(Matita_nat_nat.S(Matita_nat_nat.O))
;;

let x2 =
(Matita_nat_nat.S(x1))
;;

let x3 =
(Matita_nat_nat.S(x2))
;;

let nth =
let rec nth = 
(function l -> (function d -> (function n -> 
(match n with 
   Matita_nat_nat.O -> 
(match l with 
   Nil -> d
 | Cons(x,_) -> x)

 | Matita_nat_nat.S(n') -> (nth (tail l) d n'))
))) in nth
;;

