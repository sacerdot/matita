type word16 =
Mk_word16 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
;;

let word16_rec =
(function f -> (function w -> 
(match w with 
   Mk_word16(b,b1) -> (f b b1))
))
;;

let word16_rect =
(function f -> (function w -> 
(match w with 
   Mk_word16(b,b1) -> (f b b1))
))
;;

let w16h =
(function w -> 
(match w with 
   Mk_word16(w16h,w16l) -> w16h)
)
;;

let w16l =
(function w -> 
(match w with 
   Mk_word16(w16h,w16l) -> w16l)
)
;;

let eq_w16 =
(function w1 -> (function w2 -> (Matita_freescale_extra.and_bool (Matita_freescale_byte8.eq_b8 (w16h w1) (w16h w2)) (Matita_freescale_byte8.eq_b8 (w16l w1) (w16l w2)))))
;;

let lt_w16 =
(function w1 -> (function w2 -> 
(match (Matita_freescale_byte8.lt_b8 (w16h w1) (w16h w2)) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.True
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_byte8.gt_b8 (w16h w1) (w16h w2)) with 
   Matita_datatypes_bool.True -> Matita_datatypes_bool.False
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.lt_b8 (w16l w1) (w16l w2)))
)
))
;;

let le_w16 =
(function w1 -> (function w2 -> (Matita_freescale_extra.or_bool (eq_w16 w1 w2) (lt_w16 w1 w2))))
;;

let gt_w16 =
(function w1 -> (function w2 -> (Matita_freescale_extra.not_bool (le_w16 w1 w2))))
;;

let ge_w16 =
(function w1 -> (function w2 -> (Matita_freescale_extra.not_bool (lt_w16 w1 w2))))
;;

let and_w16 =
(function w1 -> (function w2 -> (Mk_word16((Matita_freescale_byte8.and_b8 (w16h w1) (w16h w2)),(Matita_freescale_byte8.and_b8 (w16l w1) (w16l w2))))))
;;

let or_w16 =
(function w1 -> (function w2 -> (Mk_word16((Matita_freescale_byte8.or_b8 (w16h w1) (w16h w2)),(Matita_freescale_byte8.or_b8 (w16l w1) (w16l w2))))))
;;

let xor_w16 =
(function w1 -> (function w2 -> (Mk_word16((Matita_freescale_byte8.xor_b8 (w16h w1) (w16h w2)),(Matita_freescale_byte8.xor_b8 (w16l w1) (w16l w2))))))
;;

let rcr_w16 =
(function w -> (function c -> 
(match (Matita_freescale_byte8.rcr_b8 (w16h w) c) with 
   Matita_datatypes_constructors.Pair(wh',c') -> 
(match (Matita_freescale_byte8.rcr_b8 (w16l w) c') with 
   Matita_datatypes_constructors.Pair(wl',c'') -> (Matita_datatypes_constructors.Pair((Mk_word16(wh',wl')),c'')))
)
))
;;

let shr_w16 =
(function w -> 
(match (Matita_freescale_byte8.rcr_b8 (w16h w) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(wh',c') -> 
(match (Matita_freescale_byte8.rcr_b8 (w16l w) c') with 
   Matita_datatypes_constructors.Pair(wl',c'') -> (Matita_datatypes_constructors.Pair((Mk_word16(wh',wl')),c'')))
)
)
;;

let ror_w16 =
(function w -> 
(match (Matita_freescale_byte8.rcr_b8 (w16h w) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(wh',c') -> 
(match (Matita_freescale_byte8.rcr_b8 (w16l w) c') with 
   Matita_datatypes_constructors.Pair(wl',c'') -> 
(match c'' with 
   Matita_datatypes_bool.True -> (Mk_word16((Matita_freescale_byte8.or_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X0)) wh'),wl'))
 | Matita_datatypes_bool.False -> (Mk_word16(wh',wl')))
)
)
)
;;

let ror_w16_n =
let rec ror_w16_n = 
(function w -> (function n -> 
(match n with 
   Matita_nat_nat.O -> w
 | Matita_nat_nat.S(n') -> (ror_w16_n (ror_w16 w) n'))
)) in ror_w16_n
;;

let rcl_w16 =
(function w -> (function c -> 
(match (Matita_freescale_byte8.rcl_b8 (w16l w) c) with 
   Matita_datatypes_constructors.Pair(wl',c') -> 
(match (Matita_freescale_byte8.rcl_b8 (w16h w) c') with 
   Matita_datatypes_constructors.Pair(wh',c'') -> (Matita_datatypes_constructors.Pair((Mk_word16(wh',wl')),c'')))
)
))
;;

let shl_w16 =
(function w -> 
(match (Matita_freescale_byte8.rcl_b8 (w16l w) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(wl',c') -> 
(match (Matita_freescale_byte8.rcl_b8 (w16h w) c') with 
   Matita_datatypes_constructors.Pair(wh',c'') -> (Matita_datatypes_constructors.Pair((Mk_word16(wh',wl')),c'')))
)
)
;;

let rol_w16 =
(function w -> 
(match (Matita_freescale_byte8.rcl_b8 (w16l w) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(wl',c') -> 
(match (Matita_freescale_byte8.rcl_b8 (w16h w) c') with 
   Matita_datatypes_constructors.Pair(wh',c'') -> 
(match c'' with 
   Matita_datatypes_bool.True -> (Mk_word16(wh',(Matita_freescale_byte8.or_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)) wl')))
 | Matita_datatypes_bool.False -> (Mk_word16(wh',wl')))
)
)
)
;;

let rol_w16_n =
let rec rol_w16_n = 
(function w -> (function n -> 
(match n with 
   Matita_nat_nat.O -> w
 | Matita_nat_nat.S(n') -> (rol_w16_n (rol_w16 w) n'))
)) in rol_w16_n
;;

let not_w16 =
(function w -> (Mk_word16((Matita_freescale_byte8.not_b8 (w16h w)),(Matita_freescale_byte8.not_b8 (w16l w)))))
;;

let plus_w16 =
(function w1 -> (function w2 -> (function c -> 
(match (Matita_freescale_byte8.plus_b8 (w16l w1) (w16l w2) c) with 
   Matita_datatypes_constructors.Pair(l,c') -> 
(match (Matita_freescale_byte8.plus_b8 (w16h w1) (w16h w2) c') with 
   Matita_datatypes_constructors.Pair(h,c'') -> (Matita_datatypes_constructors.Pair((Mk_word16(h,l)),c'')))
)
)))
;;

let plus_w16nc =
(function w1 -> (function w2 -> (Matita_datatypes_constructors.fst (plus_w16 w1 w2 Matita_datatypes_bool.False))))
;;

let plus_w16c =
(function w1 -> (function w2 -> (Matita_datatypes_constructors.snd (plus_w16 w1 w2 Matita_datatypes_bool.False))))
;;

let mSB_w16 =
(function w -> (Matita_freescale_exadecim.eq_ex Matita_freescale_exadecim.X8 (Matita_freescale_exadecim.and_ex Matita_freescale_exadecim.X8 (Matita_freescale_byte8.b8h (w16h w)))))
;;

let nat_of_word16 =
(function w -> (Matita_nat_plus.plus (Matita_nat_times.times (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Matita_freescale_byte8.nat_of_byte8 (w16h w))) (Matita_freescale_byte8.nat_of_byte8 (w16l w))))
;;

let word16_of_nat =
(function n -> (Mk_word16((Matita_freescale_byte8.byte8_of_nat (Matita_nat_div_and_mod.div n (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),(Matita_freescale_byte8.byte8_of_nat n))))
;;

let pred_w16 =
(function w -> 
(match (Matita_freescale_byte8.eq_b8 (w16l w) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))) with 
   Matita_datatypes_bool.True -> (Mk_word16((Matita_freescale_byte8.pred_b8 (w16h w)),(Matita_freescale_byte8.pred_b8 (w16l w))))
 | Matita_datatypes_bool.False -> (Mk_word16((w16h w),(Matita_freescale_byte8.pred_b8 (w16l w)))))
)
;;

let succ_w16 =
(function w -> 
(match (Matita_freescale_byte8.eq_b8 (w16l w) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))) with 
   Matita_datatypes_bool.True -> (Mk_word16((Matita_freescale_byte8.succ_b8 (w16h w)),(Matita_freescale_byte8.succ_b8 (w16l w))))
 | Matita_datatypes_bool.False -> (Mk_word16((w16h w),(Matita_freescale_byte8.succ_b8 (w16l w)))))
)
;;

let compl_w16 =
(function w -> 
(match (mSB_w16 w) with 
   Matita_datatypes_bool.True -> (succ_w16 (not_w16 w))
 | Matita_datatypes_bool.False -> (not_w16 (pred_w16 w)))
)
;;

let mul_b8 =
(function b1 -> (function b2 -> 
(match b1 with 
   Matita_freescale_byte8.Mk_byte8(b1h,b1l) -> 
(match b2 with 
   Matita_freescale_byte8.Mk_byte8(b2h,b2l) -> 
(match (Matita_freescale_byte8.mul_ex b1l b2l) with 
   Matita_freescale_byte8.Mk_byte8(t1_h,t1_l) -> 
(match (Matita_freescale_byte8.mul_ex b1h b2l) with 
   Matita_freescale_byte8.Mk_byte8(t2_h,t2_l) -> 
(match (Matita_freescale_byte8.mul_ex b2h b1l) with 
   Matita_freescale_byte8.Mk_byte8(t3_h,t3_l) -> 
(match (Matita_freescale_byte8.mul_ex b1h b2h) with 
   Matita_freescale_byte8.Mk_byte8(t4_h,t4_l) -> (plus_w16nc (plus_w16nc (plus_w16nc (Mk_word16((Matita_freescale_byte8.Mk_byte8(t4_h,t4_l)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) (Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,t3_h)),(Matita_freescale_byte8.Mk_byte8(t3_l,Matita_freescale_exadecim.X0))))) (Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,t2_h)),(Matita_freescale_byte8.Mk_byte8(t2_l,Matita_freescale_exadecim.X0))))) (Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(t1_h,t1_l))))))
)
)
)
)
)
))
;;

let div_b8 =
(function w -> (function b -> 
(match (Matita_freescale_byte8.eq_b8 b (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))) with 
   Matita_datatypes_bool.True -> (Matita_freescale_extra.TripleT((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF)),(w16l w),Matita_datatypes_bool.True))
 | Matita_datatypes_bool.False -> 
(match (eq_w16 w (Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (Matita_freescale_extra.TripleT((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),Matita_datatypes_bool.False))
 | Matita_datatypes_bool.False -> (let rec aux = 
(function divd -> (function divs -> (function molt -> (function q -> (function c -> (let w' = (plus_w16nc divd (compl_w16 divs)) in 
(match c with 
   Matita_nat_nat.O -> 
(match (le_w16 divs divd) with 
   Matita_datatypes_bool.True -> (Matita_freescale_extra.TripleT((Matita_freescale_byte8.or_b8 molt q),(w16l w'),(Matita_freescale_extra.not_bool (Matita_freescale_byte8.eq_b8 (w16h w') (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))
 | Matita_datatypes_bool.False -> (Matita_freescale_extra.TripleT(q,(w16l divd),(Matita_freescale_extra.not_bool (Matita_freescale_byte8.eq_b8 (w16h divd) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))))

 | Matita_nat_nat.S(c') -> 
(match (le_w16 divs divd) with 
   Matita_datatypes_bool.True -> (aux w' (ror_w16 divs) (Matita_freescale_byte8.ror_b8 molt) (Matita_freescale_byte8.or_b8 molt q) c')
 | Matita_datatypes_bool.False -> (aux divd (ror_w16 divs) (Matita_freescale_byte8.ror_b8 molt) q c'))
)
)))))) in aux w (rol_w16_n (Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),b)) (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))
)
))
;;

let in_range =
(function x -> (function inf -> (function sup -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (le_w16 inf sup) (ge_w16 x inf)) (le_w16 x sup)))))
;;

let forall_word16 =
(function p -> (Matita_freescale_byte8.forall_byte8 (function bh -> (Matita_freescale_byte8.forall_byte8 (function bl -> (p (Mk_word16(bh,bl))))))))
;;

