type oct =
O0
 | O1
 | O2
 | O3
 | O4
 | O5
 | O6
 | O7
;;

let oct_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function o -> 
(match o with 
   O0 -> p
 | O1 -> p1
 | O2 -> p2
 | O3 -> p3
 | O4 -> p4
 | O5 -> p5
 | O6 -> p6
 | O7 -> p7)
)))))))))
;;

let oct_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function o -> 
(match o with 
   O0 -> p
 | O1 -> p1
 | O2 -> p2
 | O3 -> p3
 | O4 -> p4
 | O5 -> p5
 | O6 -> p6
 | O7 -> p7)
)))))))))
;;

let exadecim_of_oct =
(function o -> 
(match o with 
   O0 -> Matita_freescale_exadecim.X0
 | O1 -> Matita_freescale_exadecim.X1
 | O2 -> Matita_freescale_exadecim.X2
 | O3 -> Matita_freescale_exadecim.X3
 | O4 -> Matita_freescale_exadecim.X4
 | O5 -> Matita_freescale_exadecim.X5
 | O6 -> Matita_freescale_exadecim.X6
 | O7 -> Matita_freescale_exadecim.X7)
)
;;

let nat_OF_oct =
(function a -> (Matita_freescale_exadecim.nat_of_exadecim (exadecim_of_oct a)))
;;

let forall_oct =
(function p -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (p O0) (p O1)) (p O2)) (p O3)) (p O4)) (p O5)) (p O6)) (p O7)))
;;

type bitrigesim =
T00
 | T01
 | T02
 | T03
 | T04
 | T05
 | T06
 | T07
 | T08
 | T09
 | T0A
 | T0B
 | T0C
 | T0D
 | T0E
 | T0F
 | T10
 | T11
 | T12
 | T13
 | T14
 | T15
 | T16
 | T17
 | T18
 | T19
 | T1A
 | T1B
 | T1C
 | T1D
 | T1E
 | T1F
;;

let bitrigesim_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function p16 -> (function p17 -> (function p18 -> (function p19 -> (function p20 -> (function p21 -> (function p22 -> (function p23 -> (function p24 -> (function p25 -> (function p26 -> (function p27 -> (function p28 -> (function p29 -> (function p30 -> (function p31 -> (function b -> 
(match b with 
   T00 -> p
 | T01 -> p1
 | T02 -> p2
 | T03 -> p3
 | T04 -> p4
 | T05 -> p5
 | T06 -> p6
 | T07 -> p7
 | T08 -> p8
 | T09 -> p9
 | T0A -> p10
 | T0B -> p11
 | T0C -> p12
 | T0D -> p13
 | T0E -> p14
 | T0F -> p15
 | T10 -> p16
 | T11 -> p17
 | T12 -> p18
 | T13 -> p19
 | T14 -> p20
 | T15 -> p21
 | T16 -> p22
 | T17 -> p23
 | T18 -> p24
 | T19 -> p25
 | T1A -> p26
 | T1B -> p27
 | T1C -> p28
 | T1D -> p29
 | T1E -> p30
 | T1F -> p31)
)))))))))))))))))))))))))))))))))
;;

let bitrigesim_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function p16 -> (function p17 -> (function p18 -> (function p19 -> (function p20 -> (function p21 -> (function p22 -> (function p23 -> (function p24 -> (function p25 -> (function p26 -> (function p27 -> (function p28 -> (function p29 -> (function p30 -> (function p31 -> (function b -> 
(match b with 
   T00 -> p
 | T01 -> p1
 | T02 -> p2
 | T03 -> p3
 | T04 -> p4
 | T05 -> p5
 | T06 -> p6
 | T07 -> p7
 | T08 -> p8
 | T09 -> p9
 | T0A -> p10
 | T0B -> p11
 | T0C -> p12
 | T0D -> p13
 | T0E -> p14
 | T0F -> p15
 | T10 -> p16
 | T11 -> p17
 | T12 -> p18
 | T13 -> p19
 | T14 -> p20
 | T15 -> p21
 | T16 -> p22
 | T17 -> p23
 | T18 -> p24
 | T19 -> p25
 | T1A -> p26
 | T1B -> p27
 | T1C -> p28
 | T1D -> p29
 | T1E -> p30
 | T1F -> p31)
)))))))))))))))))))))))))))))))))
;;

let byte8_of_bitrigesim =
(function t -> 
(match t with 
   T00 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))
 | T01 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))
 | T02 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))
 | T03 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))
 | T04 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | T05 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))
 | T06 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))
 | T07 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))
 | T08 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | T09 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))
 | T0A -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))
 | T0B -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XB))
 | T0C -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))
 | T0D -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD))
 | T0E -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))
 | T0F -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))
 | T10 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | T11 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X1))
 | T12 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))
 | T13 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X3))
 | T14 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4))
 | T15 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X5))
 | T16 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X6))
 | T17 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X7))
 | T18 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))
 | T19 -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9))
 | T1A -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))
 | T1B -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XB))
 | T1C -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))
 | T1D -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XD))
 | T1E -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XE))
 | T1F -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF)))
)
;;

let nat_OF_bitrigesim =
(function a -> (Matita_freescale_byte8.nat_of_byte8 (byte8_of_bitrigesim a)))
;;

let forall_bitrigesim =
(function p -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (p T00) (p T01)) (p T02)) (p T03)) (p T04)) (p T05)) (p T06)) (p T07)) (p T08)) (p T09)) (p T0A)) (p T0B)) (p T0C)) (p T0D)) (p T0E)) (p T0F)) (p T10)) (p T11)) (p T12)) (p T13)) (p T14)) (p T15)) (p T16)) (p T17)) (p T18)) (p T19)) (p T1A)) (p T1B)) (p T1C)) (p T1D)) (p T1E)) (p T1F)))
;;

