type byte8 =
Mk_byte8 of Matita_freescale_exadecim.exadecim * Matita_freescale_exadecim.exadecim
;;

let byte8_rec =
(function f -> (function b -> 
(match b with 
   Mk_byte8(e,e1) -> (f e e1))
))
;;

let byte8_rect =
(function f -> (function b -> 
(match b with 
   Mk_byte8(e,e1) -> (f e e1))
))
;;

let b8h =
(function w -> 
(match w with 
   Mk_byte8(b8h,b8l) -> b8h)
)
;;

let b8l =
(function w -> 
(match w with 
   Mk_byte8(b8h,b8l) -> b8l)
)
;;

let eq_b8 =
(function b1 -> (function b2 -> (Matita_freescale_extra.and_bool (Matita_freescale_exadecim.eq_ex (b8h b1) (b8h b2)) (Matita_freescale_exadecim.eq_ex (b8l b1) (b8l b2)))))
;;

let lt_b8 =
(function b1 -> (function b2 -> 
(match (Matita_freescale_exadecim.lt_ex (b8h b1) (b8h b2)) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.True
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_exadecim.gt_ex (b8h b1) (b8h b2)) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.False
 | Matita_datatypes_bool.False -> (Matita_freescale_exadecim.lt_ex (b8l b1) (b8l b2)))
)
))
;;

let le_b8 =
(function b1 -> (function b2 -> (Matita_freescale_extra.or_bool (eq_b8 b1 b2) (lt_b8 b1 b2))))
;;

let gt_b8 =
(function b1 -> (function b2 -> (Matita_freescale_extra.not_bool (le_b8 b1 b2))))
;;

let ge_b8 =
(function b1 -> (function b2 -> (Matita_freescale_extra.not_bool (lt_b8 b1 b2))))
;;

let and_b8 =
(function b1 -> (function b2 -> (Mk_byte8((Matita_freescale_exadecim.and_ex (b8h b1) (b8h b2)),(Matita_freescale_exadecim.and_ex (b8l b1) (b8l b2))))))
;;

let or_b8 =
(function b1 -> (function b2 -> (Mk_byte8((Matita_freescale_exadecim.or_ex (b8h b1) (b8h b2)),(Matita_freescale_exadecim.or_ex (b8l b1) (b8l b2))))))
;;

let xor_b8 =
(function b1 -> (function b2 -> (Mk_byte8((Matita_freescale_exadecim.xor_ex (b8h b1) (b8h b2)),(Matita_freescale_exadecim.xor_ex (b8l b1) (b8l b2))))))
;;

let rcr_b8 =
(function b -> (function c -> 
(match (Matita_freescale_exadecim.rcr_ex (b8h b) c) with 
   Matita_datatypes_constructors.Pair(bh',c') -> 
(match (Matita_freescale_exadecim.rcr_ex (b8l b) c') with 
   Matita_datatypes_constructors.Pair(bl',c'') -> (Matita_datatypes_constructors.Pair((Mk_byte8(bh',bl')),c'')))
)
))
;;

let shr_b8 =
(function b -> 
(match (Matita_freescale_exadecim.rcr_ex (b8h b) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(bh',c') -> 
(match (Matita_freescale_exadecim.rcr_ex (b8l b) c') with 
   Matita_datatypes_constructors.Pair(bl',c'') -> (Matita_datatypes_constructors.Pair((Mk_byte8(bh',bl')),c'')))
)
)
;;

let ror_b8 =
(function b -> 
(match (Matita_freescale_exadecim.rcr_ex (b8h b) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(bh',c') -> 
(match (Matita_freescale_exadecim.rcr_ex (b8l b) c') with 
   Matita_datatypes_constructors.Pair(bl',c'') -> 
(match c'' with 
   Matita_datatypes_bool.True -> (Mk_byte8((Matita_freescale_exadecim.or_ex Matita_freescale_exadecim.X8 bh'),bl'))
 | Matita_datatypes_bool.False -> (Mk_byte8(bh',bl')))
)
)
)
;;

let ror_b8_n =
let rec ror_b8_n = 
(function b -> (function n -> 
(match n with 
   Matita_nat_nat.O -> b
 | Matita_nat_nat.S(n') -> (ror_b8_n (ror_b8 b) n'))
)) in ror_b8_n
;;

let rcl_b8 =
(function b -> (function c -> 
(match (Matita_freescale_exadecim.rcl_ex (b8l b) c) with 
   Matita_datatypes_constructors.Pair(bl',c') -> 
(match (Matita_freescale_exadecim.rcl_ex (b8h b) c') with 
   Matita_datatypes_constructors.Pair(bh',c'') -> (Matita_datatypes_constructors.Pair((Mk_byte8(bh',bl')),c'')))
)
))
;;

let shl_b8 =
(function b -> 
(match (Matita_freescale_exadecim.rcl_ex (b8l b) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(bl',c') -> 
(match (Matita_freescale_exadecim.rcl_ex (b8h b) c') with 
   Matita_datatypes_constructors.Pair(bh',c'') -> (Matita_datatypes_constructors.Pair((Mk_byte8(bh',bl')),c'')))
)
)
;;

let rol_b8 =
(function b -> 
(match (Matita_freescale_exadecim.rcl_ex (b8l b) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(bl',c') -> 
(match (Matita_freescale_exadecim.rcl_ex (b8h b) c') with 
   Matita_datatypes_constructors.Pair(bh',c'') -> 
(match c'' with 
   Matita_datatypes_bool.True -> (Mk_byte8(bh',(Matita_freescale_exadecim.or_ex Matita_freescale_exadecim.X1 bl')))
 | Matita_datatypes_bool.False -> (Mk_byte8(bh',bl')))
)
)
)
;;

let rol_b8_n =
let rec rol_b8_n = 
(function b -> (function n -> 
(match n with 
   Matita_nat_nat.O -> b
 | Matita_nat_nat.S(n') -> (rol_b8_n (rol_b8 b) n'))
)) in rol_b8_n
;;

let not_b8 =
(function b -> (Mk_byte8((Matita_freescale_exadecim.not_ex (b8h b)),(Matita_freescale_exadecim.not_ex (b8l b)))))
;;

let plus_b8 =
(function b1 -> (function b2 -> (function c -> 
(match (Matita_freescale_exadecim.plus_ex (b8l b1) (b8l b2) c) with 
   Matita_datatypes_constructors.Pair(l,c') -> 
(match (Matita_freescale_exadecim.plus_ex (b8h b1) (b8h b2) c') with 
   Matita_datatypes_constructors.Pair(h,c'') -> (Matita_datatypes_constructors.Pair((Mk_byte8(h,l)),c'')))
)
)))
;;

let plus_b8nc =
(function b1 -> (function b2 -> (Matita_datatypes_constructors.fst (plus_b8 b1 b2 Matita_datatypes_bool.False))))
;;

let plus_b8c =
(function b1 -> (function b2 -> (Matita_datatypes_constructors.snd (plus_b8 b1 b2 Matita_datatypes_bool.False))))
;;

let mSB_b8 =
(function b -> (Matita_freescale_exadecim.eq_ex Matita_freescale_exadecim.X8 (Matita_freescale_exadecim.and_ex Matita_freescale_exadecim.X8 (b8h b))))
;;

let nat_of_byte8 =
(function b -> (Matita_nat_plus.plus (Matita_nat_times.times (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))) (Matita_freescale_exadecim.nat_of_exadecim (b8h b))) (Matita_freescale_exadecim.nat_of_exadecim (b8l b))))
;;

let byte8_of_nat =
(function n -> (Mk_byte8((Matita_freescale_exadecim.exadecim_of_nat (Matita_nat_div_and_mod.div n (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))))),(Matita_freescale_exadecim.exadecim_of_nat n))))
;;

let pred_b8 =
(function b -> 
(match (Matita_freescale_exadecim.eq_ex (b8l b) Matita_freescale_exadecim.X0) with 
   Matita_datatypes_bool.True -> (Mk_byte8((Matita_freescale_exadecim.pred_ex (b8h b)),(Matita_freescale_exadecim.pred_ex (b8l b))))
 | Matita_datatypes_bool.False -> (Mk_byte8((b8h b),(Matita_freescale_exadecim.pred_ex (b8l b)))))
)
;;

let succ_b8 =
(function b -> 
(match (Matita_freescale_exadecim.eq_ex (b8l b) Matita_freescale_exadecim.XF) with 
   Matita_datatypes_bool.True -> (Mk_byte8((Matita_freescale_exadecim.succ_ex (b8h b)),(Matita_freescale_exadecim.succ_ex (b8l b))))
 | Matita_datatypes_bool.False -> (Mk_byte8((b8h b),(Matita_freescale_exadecim.succ_ex (b8l b)))))
)
;;

let compl_b8 =
(function b -> 
(match (mSB_b8 b) with 
   Matita_datatypes_bool.True -> (succ_b8 (not_b8 b))
 | Matita_datatypes_bool.False -> (not_b8 (pred_b8 b)))
)
;;

let mul_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   Matita_freescale_exadecim.X0 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))

 | Matita_freescale_exadecim.X1 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF)))

 | Matita_freescale_exadecim.X2 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE)))

 | Matita_freescale_exadecim.X3 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XD)))

 | Matita_freescale_exadecim.X4 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC)))

 | Matita_freescale_exadecim.X5 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XB)))

 | Matita_freescale_exadecim.X6 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XA)))

 | Matita_freescale_exadecim.X7 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X9)))

 | Matita_freescale_exadecim.X8 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X8)))

 | Matita_freescale_exadecim.X9 -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X7)))

 | Matita_freescale_exadecim.XA -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.X6)))

 | Matita_freescale_exadecim.XB -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.XA,Matita_freescale_exadecim.X5)))

 | Matita_freescale_exadecim.XC -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.XA,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.X4)))

 | Matita_freescale_exadecim.XD -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X1))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.XA,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X3)))

 | Matita_freescale_exadecim.XE -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.XA,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.XD,Matita_freescale_exadecim.X2)))

 | Matita_freescale_exadecim.XF -> 
(match e2 with 
   Matita_freescale_exadecim.X0 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | Matita_freescale_exadecim.X1 -> (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))
 | Matita_freescale_exadecim.X2 -> (Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | Matita_freescale_exadecim.X3 -> (Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XD))
 | Matita_freescale_exadecim.X4 -> (Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))
 | Matita_freescale_exadecim.X5 -> (Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XB))
 | Matita_freescale_exadecim.X6 -> (Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XA))
 | Matita_freescale_exadecim.X7 -> (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X9))
 | Matita_freescale_exadecim.X8 -> (Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X8))
 | Matita_freescale_exadecim.X9 -> (Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X7))
 | Matita_freescale_exadecim.XA -> (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.X6))
 | Matita_freescale_exadecim.XB -> (Mk_byte8(Matita_freescale_exadecim.XA,Matita_freescale_exadecim.X5))
 | Matita_freescale_exadecim.XC -> (Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.X4))
 | Matita_freescale_exadecim.XD -> (Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X3))
 | Matita_freescale_exadecim.XE -> (Mk_byte8(Matita_freescale_exadecim.XD,Matita_freescale_exadecim.X2))
 | Matita_freescale_exadecim.XF -> (Mk_byte8(Matita_freescale_exadecim.XE,Matita_freescale_exadecim.X1)))
)
))
;;

let daa_b8 =
(function h -> (function c -> (function x -> 
(match (lt_b8 x (Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XA))) with 
   Matita_datatypes_bool.True -> (let x' = 
(match (Matita_freescale_extra.and_bool (Matita_freescale_exadecim.lt_ex (b8l x) Matita_freescale_exadecim.XA) (Matita_freescale_extra.not_bool h)) with 
   Matita_datatypes_bool.True -> x
 | Matita_datatypes_bool.False -> (plus_b8nc x (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))
 in (let x'' = 
(match c with 
   Matita_datatypes_bool.True -> (plus_b8nc x' (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X0)))
 | Matita_datatypes_bool.False -> x')
 in (Matita_datatypes_constructors.Pair(x'',c))))
 | Matita_datatypes_bool.False -> (let x' = 
(match (Matita_freescale_extra.and_bool (Matita_freescale_exadecim.lt_ex (b8l x) Matita_freescale_exadecim.XA) (Matita_freescale_extra.not_bool h)) with 
   Matita_datatypes_bool.True -> x
 | Matita_datatypes_bool.False -> (plus_b8nc x (Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))
 in (let x'' = (plus_b8nc x' (Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X0))) in (Matita_datatypes_constructors.Pair(x'',Matita_datatypes_bool.True)))))
)))
;;

let forall_byte8 =
(function p -> (Matita_freescale_exadecim.forall_exadecim (function bh -> (Matita_freescale_exadecim.forall_exadecim (function bl -> (p (Mk_byte8(bh,bl))))))))
;;

