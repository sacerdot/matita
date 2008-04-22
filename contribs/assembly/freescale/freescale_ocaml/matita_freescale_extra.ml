let not_bool =
(function b -> 
(match b with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.False
 | Matita_datatypes_bool.False -> Matita_datatypes_bool.True)
)
;;

let and_bool =
(function b1 -> (function b2 -> 
(match b1 with 
   Matita_datatypes_bool.True -> b2
 | Matita_datatypes_bool.False -> Matita_datatypes_bool.False)
))
;;

let or_bool =
(function b1 -> (function b2 -> 
(match b1 with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.True
 | Matita_datatypes_bool.False -> b2)
))
;;

let xor_bool =
(function b1 -> (function b2 -> 
(match b1 with 
   Matita_datatypes_bool.True -> (not_bool b2)
 | Matita_datatypes_bool.False -> b2)
))
;;

let eq_bool =
(function b1 -> (function b2 -> 
(match b1 with 
   Matita_datatypes_bool.True -> b2
 | Matita_datatypes_bool.False -> (not_bool b2))
))
;;

type ('t1,'t2,'t3) prod3T =
TripleT of 't1 * 't2 * 't3
;;

let prod3T_rec =
(function f -> (function p -> 
(match p with 
   TripleT(t,t1,t2) -> (f t t1 t2))
))
;;

let prod3T_rect =
(function f -> (function p -> 
(match p with 
   TripleT(t,t1,t2) -> (f t t1 t2))
))
;;

let fst3T =
(function p -> 
(match p with 
   TripleT(x,_,_) -> x)
)
;;

let snd3T =
(function p -> 
(match p with 
   TripleT(_,x,_) -> x)
)
;;

let thd3T =
(function p -> 
(match p with 
   TripleT(_,_,x) -> x)
)
;;

type ('t1,'t2,'t3,'t4) prod4T =
QuadrupleT of 't1 * 't2 * 't3 * 't4
;;

let prod4T_rec =
(function f -> (function p -> 
(match p with 
   QuadrupleT(t,t1,t2,t3) -> (f t t1 t2 t3))
))
;;

let prod4T_rect =
(function f -> (function p -> 
(match p with 
   QuadrupleT(t,t1,t2,t3) -> (f t t1 t2 t3))
))
;;

let fst4T =
(function p -> 
(match p with 
   QuadrupleT(x,_,_,_) -> x)
)
;;

let snd4T =
(function p -> 
(match p with 
   QuadrupleT(_,x,_,_) -> x)
)
;;

let thd4T =
(function p -> 
(match p with 
   QuadrupleT(_,_,x,_) -> x)
)
;;

let fth4T =
(function p -> 
(match p with 
   QuadrupleT(_,_,_,x) -> x)
)
;;

type ('t1,'t2,'t3,'t4,'t5) prod5T =
QuintupleT of 't1 * 't2 * 't3 * 't4 * 't5
;;

let prod5T_rec =
(function f -> (function p -> 
(match p with 
   QuintupleT(t,t1,t2,t3,t4) -> (f t t1 t2 t3 t4))
))
;;

let prod5T_rect =
(function f -> (function p -> 
(match p with 
   QuintupleT(t,t1,t2,t3,t4) -> (f t t1 t2 t3 t4))
))
;;

let fst5T =
(function p -> 
(match p with 
   QuintupleT(x,_,_,_,_) -> x)
)
;;

let snd5T =
(function p -> 
(match p with 
   QuintupleT(_,x,_,_,_) -> x)
)
;;

let thd5T =
(function p -> 
(match p with 
   QuintupleT(_,_,x,_,_) -> x)
)
;;

let frth5T =
(function p -> 
(match p with 
   QuintupleT(_,_,_,x,_) -> x)
)
;;

let ffth5T =
(function p -> 
(match p with 
   QuintupleT(_,_,_,_,x) -> x)
)
;;

let opt_map =
(function t -> (function f -> 
(match t with 
   Matita_datatypes_constructors.None -> (Matita_datatypes_constructors.None)
 | Matita_datatypes_constructors.Some(x) -> (f x))
))
;;

let nat_of_bool =
(function b -> 
(match b with 
   Matita_datatypes_bool.True -> (Matita_nat_nat.S(Matita_nat_nat.O))
 | Matita_datatypes_bool.False -> Matita_nat_nat.O)
)
;;

