type memory_type =
MEM_READ_ONLY
 | MEM_READ_WRITE
 | MEM_OUT_OF_BOUND
;;

let memory_type_rec =
(function p -> (function p1 -> (function p2 -> (function m -> 
(match m with 
   MEM_READ_ONLY -> p
 | MEM_READ_WRITE -> p1
 | MEM_OUT_OF_BOUND -> p2)
))))
;;

let memory_type_rect =
(function p -> (function p1 -> (function p2 -> (function m -> 
(match m with 
   MEM_READ_ONLY -> p
 | MEM_READ_WRITE -> p1
 | MEM_OUT_OF_BOUND -> p2)
))))
;;

type ('t) prod16T =
Array_16T of 't * 't * 't * 't * 't * 't * 't * 't * 't * 't * 't * 't * 't * 't * 't * 't
;;

let prod16T_rec =
(function f -> (function p -> 
(match p with 
   Array_16T(t,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15) -> (f t t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15))
))
;;

let prod16T_rect =
(function f -> (function p -> 
(match p with 
   Array_16T(t,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15) -> (f t t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15))
))
;;

let getn_array16T =
(function n -> (function p -> 
(match p with 
   Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15) -> 
(match n with 
   Matita_freescale_exadecim.X0 -> e00
 | Matita_freescale_exadecim.X1 -> e01
 | Matita_freescale_exadecim.X2 -> e02
 | Matita_freescale_exadecim.X3 -> e03
 | Matita_freescale_exadecim.X4 -> e04
 | Matita_freescale_exadecim.X5 -> e05
 | Matita_freescale_exadecim.X6 -> e06
 | Matita_freescale_exadecim.X7 -> e07
 | Matita_freescale_exadecim.X8 -> e08
 | Matita_freescale_exadecim.X9 -> e09
 | Matita_freescale_exadecim.XA -> e10
 | Matita_freescale_exadecim.XB -> e11
 | Matita_freescale_exadecim.XC -> e12
 | Matita_freescale_exadecim.XD -> e13
 | Matita_freescale_exadecim.XE -> e14
 | Matita_freescale_exadecim.XF -> e15)
)
))
;;

let setn_array16T =
(function n -> (function p -> (function v -> 
(match p with 
   Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15) -> 
(match n with 
   Matita_freescale_exadecim.X0 -> (Array_16T(v,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X1 -> (Array_16T(e00,v,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X2 -> (Array_16T(e00,e01,v,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X3 -> (Array_16T(e00,e01,e02,v,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X4 -> (Array_16T(e00,e01,e02,e03,v,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X5 -> (Array_16T(e00,e01,e02,e03,e04,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,e01,e02,e03,e04,e05,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,v)))
)
)))
;;

let setmn_array16T =
(function m -> (function n -> (function p -> (function v -> 
(match p with 
   Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15) -> 
(match m with 
   Matita_freescale_exadecim.X0 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> (Array_16T(v,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X1 -> (Array_16T(v,v,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X2 -> (Array_16T(v,v,v,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X3 -> (Array_16T(v,v,v,v,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X4 -> (Array_16T(v,v,v,v,v,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X5 -> (Array_16T(v,v,v,v,v,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(v,v,v,v,v,v,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(v,v,v,v,v,v,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(v,v,v,v,v,v,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(v,v,v,v,v,v,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(v,v,v,v,v,v,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(v,v,v,v,v,v,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(v,v,v,v,v,v,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(v,v,v,v,v,v,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(v,v,v,v,v,v,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(v,v,v,v,v,v,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X1 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> (Array_16T(e00,v,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X2 -> (Array_16T(e00,v,v,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X3 -> (Array_16T(e00,v,v,v,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X4 -> (Array_16T(e00,v,v,v,v,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X5 -> (Array_16T(e00,v,v,v,v,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,v,v,v,v,v,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,v,v,v,v,v,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,v,v,v,v,v,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,v,v,v,v,v,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X2 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> (Array_16T(e00,e01,v,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X3 -> (Array_16T(e00,e01,v,v,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X4 -> (Array_16T(e00,e01,v,v,v,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X5 -> (Array_16T(e00,e01,v,v,v,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,e01,v,v,v,v,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,v,v,v,v,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,v,v,v,v,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,v,v,v,v,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X3 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> (Array_16T(e00,e01,e02,v,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X4 -> (Array_16T(e00,e01,e02,v,v,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X5 -> (Array_16T(e00,e01,e02,v,v,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,e01,e02,v,v,v,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,e02,v,v,v,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,v,v,v,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X4 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> (Array_16T(e00,e01,e02,e03,v,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X5 -> (Array_16T(e00,e01,e02,e03,v,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,e01,e02,e03,v,v,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,e02,e03,v,v,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,v,v,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X5 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> (Array_16T(e00,e01,e02,e03,e04,v,e06,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,e01,e02,e03,e04,v,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,v,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X6 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> (Array_16T(e00,e01,e02,e03,e04,e05,v,e07,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,v,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X7 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,e08,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,v,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X8 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,e09,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,v,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.X9 -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,e10,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,v,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.XA -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> p
 | Matita_freescale_exadecim.XA -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,e11,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,v,v,v,v,v,v)))

 | Matita_freescale_exadecim.XB -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> p
 | Matita_freescale_exadecim.XA -> p
 | Matita_freescale_exadecim.XB -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,v,e12,e13,e14,e15))
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,v,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,v,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,v,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,v,v,v,v,v)))

 | Matita_freescale_exadecim.XC -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> p
 | Matita_freescale_exadecim.XA -> p
 | Matita_freescale_exadecim.XB -> p
 | Matita_freescale_exadecim.XC -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,v,e13,e14,e15))
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,v,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,v,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,v,v,v,v)))

 | Matita_freescale_exadecim.XD -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> p
 | Matita_freescale_exadecim.XA -> p
 | Matita_freescale_exadecim.XB -> p
 | Matita_freescale_exadecim.XC -> p
 | Matita_freescale_exadecim.XD -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,v,e14,e15))
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,v,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,v,v,v)))

 | Matita_freescale_exadecim.XE -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> p
 | Matita_freescale_exadecim.XA -> p
 | Matita_freescale_exadecim.XB -> p
 | Matita_freescale_exadecim.XC -> p
 | Matita_freescale_exadecim.XD -> p
 | Matita_freescale_exadecim.XE -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,v,e15))
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,v,v)))

 | Matita_freescale_exadecim.XF -> 
(match n with 
   Matita_freescale_exadecim.X0 -> p
 | Matita_freescale_exadecim.X1 -> p
 | Matita_freescale_exadecim.X2 -> p
 | Matita_freescale_exadecim.X3 -> p
 | Matita_freescale_exadecim.X4 -> p
 | Matita_freescale_exadecim.X5 -> p
 | Matita_freescale_exadecim.X6 -> p
 | Matita_freescale_exadecim.X7 -> p
 | Matita_freescale_exadecim.X8 -> p
 | Matita_freescale_exadecim.X9 -> p
 | Matita_freescale_exadecim.XA -> p
 | Matita_freescale_exadecim.XB -> p
 | Matita_freescale_exadecim.XC -> p
 | Matita_freescale_exadecim.XD -> p
 | Matita_freescale_exadecim.XE -> p
 | Matita_freescale_exadecim.XF -> (Array_16T(e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e10,e11,e12,e13,e14,v)))
)
)
))))
;;

let setmn_array16T_succ_pred =
(function m -> (function n -> (function p -> (function v -> 
(match (Matita_freescale_exadecim.lt_ex m Matita_freescale_exadecim.XF) with 
   Matita_datatypes_bool.True -> 
(match (Matita_freescale_exadecim.gt_ex n Matita_freescale_exadecim.X0) with 
   Matita_datatypes_bool.True -> (setmn_array16T (Matita_freescale_exadecim.succ_ex m) (Matita_freescale_exadecim.pred_ex n) p v)
 | Matita_datatypes_bool.False -> p)

 | Matita_datatypes_bool.False -> p)
))))
;;

let setmn_array16T_succ =
(function m -> (function p -> (function v -> 
(match (Matita_freescale_exadecim.lt_ex m Matita_freescale_exadecim.XF) with 
   Matita_datatypes_bool.True -> (setmn_array16T (Matita_freescale_exadecim.succ_ex m) Matita_freescale_exadecim.XF p v)
 | Matita_datatypes_bool.False -> p)
)))
;;

let setmn_array16T_pred =
(function n -> (function p -> (function v -> 
(match (Matita_freescale_exadecim.gt_ex n Matita_freescale_exadecim.X0) with 
   Matita_datatypes_bool.True -> (setmn_array16T Matita_freescale_exadecim.X0 (Matita_freescale_exadecim.pred_ex n) p v)
 | Matita_datatypes_bool.False -> p)
)))
;;

type ('t) prod8T =
Array_8T of 't * 't * 't * 't * 't * 't * 't * 't
;;

let prod8T_rec =
(function f -> (function p -> 
(match p with 
   Array_8T(t,t1,t2,t3,t4,t5,t6,t7) -> (f t t1 t2 t3 t4 t5 t6 t7))
))
;;

let prod8T_rect =
(function f -> (function p -> 
(match p with 
   Array_8T(t,t1,t2,t3,t4,t5,t6,t7) -> (f t t1 t2 t3 t4 t5 t6 t7))
))
;;

let getn_array8T =
(function n -> (function p -> 
(match p with 
   Array_8T(e07,e06,e05,e04,e03,e02,e01,e00) -> 
(match n with 
   Matita_freescale_aux_bases.O0 -> e00
 | Matita_freescale_aux_bases.O1 -> e01
 | Matita_freescale_aux_bases.O2 -> e02
 | Matita_freescale_aux_bases.O3 -> e03
 | Matita_freescale_aux_bases.O4 -> e04
 | Matita_freescale_aux_bases.O5 -> e05
 | Matita_freescale_aux_bases.O6 -> e06
 | Matita_freescale_aux_bases.O7 -> e07)
)
))
;;

let setn_array8T =
(function n -> (function p -> (function v -> 
(match p with 
   Array_8T(e07,e06,e05,e04,e03,e02,e01,e00) -> 
(match n with 
   Matita_freescale_aux_bases.O0 -> (Array_8T(e07,e06,e05,e04,e03,e02,e01,v))
 | Matita_freescale_aux_bases.O1 -> (Array_8T(e07,e06,e05,e04,e03,e02,v,e00))
 | Matita_freescale_aux_bases.O2 -> (Array_8T(e07,e06,e05,e04,e03,v,e01,e00))
 | Matita_freescale_aux_bases.O3 -> (Array_8T(e07,e06,e05,e04,v,e02,e01,e00))
 | Matita_freescale_aux_bases.O4 -> (Array_8T(e07,e06,e05,v,e03,e02,e01,e00))
 | Matita_freescale_aux_bases.O5 -> (Array_8T(e07,e06,v,e04,e03,e02,e01,e00))
 | Matita_freescale_aux_bases.O6 -> (Array_8T(e07,v,e05,e04,e03,e02,e01,e00))
 | Matita_freescale_aux_bases.O7 -> (Array_8T(v,e06,e05,e04,e03,e02,e01,e00)))
)
)))
;;

let byte8_of_bits =
(function p -> 
(match p with 
   Array_8T(e07,e06,e05,e04,e03,e02,e01,e00) -> (Matita_freescale_byte8.Mk_byte8((Matita_freescale_exadecim.or_ex 
(match e07 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X8
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
 (Matita_freescale_exadecim.or_ex 
(match e06 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X4
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
 (Matita_freescale_exadecim.or_ex 
(match e05 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X2
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
 
(match e04 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X1
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
))),(Matita_freescale_exadecim.or_ex 
(match e03 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X8
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
 (Matita_freescale_exadecim.or_ex 
(match e02 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X4
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
 (Matita_freescale_exadecim.or_ex 
(match e01 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X2
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
 
(match e00 with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X1
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
))))))
)
;;

let bits_of_byte8 =
(function p -> 
(match (Matita_freescale_byte8.b8h p) with 
   Matita_freescale_exadecim.X0 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X1 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X2 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X3 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X4 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X5 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X6 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X7 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X8 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.X9 -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.XA -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.XB -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.XC -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.XD -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.XE -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))

 | Matita_freescale_exadecim.XF -> 
(match (Matita_freescale_byte8.b8l p) with 
   Matita_freescale_exadecim.X0 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X1 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X2 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X3 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X4 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X5 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X6 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X7 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.X8 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.X9 -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XA -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XB -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XC -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XD -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False,Matita_datatypes_bool.True))
 | Matita_freescale_exadecim.XE -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.False))
 | Matita_freescale_exadecim.XF -> (Array_8T(Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True,Matita_datatypes_bool.True)))
)
)
;;

