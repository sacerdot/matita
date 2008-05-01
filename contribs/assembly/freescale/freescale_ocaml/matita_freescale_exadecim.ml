type exadecim =
X0
 | X1
 | X2
 | X3
 | X4
 | X5
 | X6
 | X7
 | X8
 | X9
 | XA
 | XB
 | XC
 | XD
 | XE
 | XF
;;

let exadecim_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function e -> 
(match e with 
   X0 -> p
 | X1 -> p1
 | X2 -> p2
 | X3 -> p3
 | X4 -> p4
 | X5 -> p5
 | X6 -> p6
 | X7 -> p7
 | X8 -> p8
 | X9 -> p9
 | XA -> p10
 | XB -> p11
 | XC -> p12
 | XD -> p13
 | XE -> p14
 | XF -> p15)
)))))))))))))))))
;;

let exadecim_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function p5 -> (function p6 -> (function p7 -> (function p8 -> (function p9 -> (function p10 -> (function p11 -> (function p12 -> (function p13 -> (function p14 -> (function p15 -> (function e -> 
(match e with 
   X0 -> p
 | X1 -> p1
 | X2 -> p2
 | X3 -> p3
 | X4 -> p4
 | X5 -> p5
 | X6 -> p6
 | X7 -> p7
 | X8 -> p8
 | X9 -> p9
 | XA -> p10
 | XB -> p11
 | XC -> p12
 | XD -> p13
 | XE -> p14
 | XF -> p15)
)))))))))))))))))
;;

let eq_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X1 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X2 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X3 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X4 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X5 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X6 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X7 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X8 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X9 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XA -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XB -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XC -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XD -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XE -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.False)

 | XF -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.True)
)
))
;;

let lt_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X1 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X2 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X3 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X4 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X5 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X6 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X7 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X8 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X9 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XA -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XB -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XC -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XD -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XE -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.True)

 | XF -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)
)
))
;;

let le_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X1 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X2 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X3 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X4 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X5 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X6 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X7 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X8 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | X9 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XA -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XB -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XC -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XD -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XE -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)

 | XF -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.True)
)
))
;;

let gt_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X1 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X2 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X3 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X4 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X5 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X6 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X7 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X8 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X9 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XA -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XB -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XC -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XD -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XE -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XF -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.False)
)
))
;;

let ge_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X1 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X2 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X3 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X4 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X5 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X6 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X7 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.False
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X8 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.False
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | X9 -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.False
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XA -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.False
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XB -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.False
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XC -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.False
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XD -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.False
 | XF -> Matita_datatypes_bool.False)

 | XE -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.False)

 | XF -> 
(match e2 with 
   X0 -> Matita_datatypes_bool.True
 | X1 -> Matita_datatypes_bool.True
 | X2 -> Matita_datatypes_bool.True
 | X3 -> Matita_datatypes_bool.True
 | X4 -> Matita_datatypes_bool.True
 | X5 -> Matita_datatypes_bool.True
 | X6 -> Matita_datatypes_bool.True
 | X7 -> Matita_datatypes_bool.True
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)
)
))
;;

let and_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X0
 | X3 -> X0
 | X4 -> X0
 | X5 -> X0
 | X6 -> X0
 | X7 -> X0
 | X8 -> X0
 | X9 -> X0
 | XA -> X0
 | XB -> X0
 | XC -> X0
 | XD -> X0
 | XE -> X0
 | XF -> X0)

 | X1 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X0
 | X3 -> X1
 | X4 -> X0
 | X5 -> X1
 | X6 -> X0
 | X7 -> X1
 | X8 -> X0
 | X9 -> X1
 | XA -> X0
 | XB -> X1
 | XC -> X0
 | XD -> X1
 | XE -> X0
 | XF -> X1)

 | X2 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X2
 | X3 -> X2
 | X4 -> X0
 | X5 -> X0
 | X6 -> X2
 | X7 -> X2
 | X8 -> X0
 | X9 -> X0
 | XA -> X2
 | XB -> X2
 | XC -> X0
 | XD -> X0
 | XE -> X2
 | XF -> X2)

 | X3 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X2
 | X3 -> X3
 | X4 -> X0
 | X5 -> X1
 | X6 -> X2
 | X7 -> X3
 | X8 -> X0
 | X9 -> X1
 | XA -> X2
 | XB -> X3
 | XC -> X0
 | XD -> X1
 | XE -> X2
 | XF -> X3)

 | X4 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X0
 | X3 -> X0
 | X4 -> X4
 | X5 -> X4
 | X6 -> X4
 | X7 -> X4
 | X8 -> X0
 | X9 -> X0
 | XA -> X0
 | XB -> X0
 | XC -> X4
 | XD -> X4
 | XE -> X4
 | XF -> X4)

 | X5 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X0
 | X3 -> X1
 | X4 -> X4
 | X5 -> X5
 | X6 -> X4
 | X7 -> X5
 | X8 -> X0
 | X9 -> X1
 | XA -> X0
 | XB -> X1
 | XC -> X4
 | XD -> X5
 | XE -> X4
 | XF -> X5)

 | X6 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X2
 | X3 -> X2
 | X4 -> X4
 | X5 -> X4
 | X6 -> X6
 | X7 -> X6
 | X8 -> X0
 | X9 -> X0
 | XA -> X2
 | XB -> X2
 | XC -> X4
 | XD -> X4
 | XE -> X6
 | XF -> X6)

 | X7 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X2
 | X3 -> X3
 | X4 -> X4
 | X5 -> X5
 | X6 -> X6
 | X7 -> X7
 | X8 -> X0
 | X9 -> X1
 | XA -> X2
 | XB -> X3
 | XC -> X4
 | XD -> X5
 | XE -> X6
 | XF -> X7)

 | X8 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X0
 | X3 -> X0
 | X4 -> X0
 | X5 -> X0
 | X6 -> X0
 | X7 -> X0
 | X8 -> X8
 | X9 -> X8
 | XA -> X8
 | XB -> X8
 | XC -> X8
 | XD -> X8
 | XE -> X8
 | XF -> X8)

 | X9 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X0
 | X3 -> X1
 | X4 -> X0
 | X5 -> X1
 | X6 -> X0
 | X7 -> X1
 | X8 -> X8
 | X9 -> X9
 | XA -> X8
 | XB -> X9
 | XC -> X8
 | XD -> X9
 | XE -> X8
 | XF -> X9)

 | XA -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X2
 | X3 -> X2
 | X4 -> X0
 | X5 -> X0
 | X6 -> X2
 | X7 -> X2
 | X8 -> X8
 | X9 -> X8
 | XA -> XA
 | XB -> XA
 | XC -> X8
 | XD -> X8
 | XE -> XA
 | XF -> XA)

 | XB -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X2
 | X3 -> X3
 | X4 -> X0
 | X5 -> X1
 | X6 -> X2
 | X7 -> X3
 | X8 -> X8
 | X9 -> X9
 | XA -> XA
 | XB -> XB
 | XC -> X8
 | XD -> X9
 | XE -> XA
 | XF -> XB)

 | XC -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X0
 | X3 -> X0
 | X4 -> X4
 | X5 -> X4
 | X6 -> X4
 | X7 -> X4
 | X8 -> X8
 | X9 -> X8
 | XA -> X8
 | XB -> X8
 | XC -> XC
 | XD -> XC
 | XE -> XC
 | XF -> XC)

 | XD -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X0
 | X3 -> X1
 | X4 -> X4
 | X5 -> X5
 | X6 -> X4
 | X7 -> X5
 | X8 -> X8
 | X9 -> X9
 | XA -> X8
 | XB -> X9
 | XC -> XC
 | XD -> XD
 | XE -> XC
 | XF -> XD)

 | XE -> 
(match e2 with 
   X0 -> X0
 | X1 -> X0
 | X2 -> X2
 | X3 -> X2
 | X4 -> X4
 | X5 -> X4
 | X6 -> X6
 | X7 -> X6
 | X8 -> X8
 | X9 -> X8
 | XA -> XA
 | XB -> XA
 | XC -> XC
 | XD -> XC
 | XE -> XE
 | XF -> XE)

 | XF -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X2
 | X3 -> X3
 | X4 -> X4
 | X5 -> X5
 | X6 -> X6
 | X7 -> X7
 | X8 -> X8
 | X9 -> X9
 | XA -> XA
 | XB -> XB
 | XC -> XC
 | XD -> XD
 | XE -> XE
 | XF -> XF)
)
))
;;

let or_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X2
 | X3 -> X3
 | X4 -> X4
 | X5 -> X5
 | X6 -> X6
 | X7 -> X7
 | X8 -> X8
 | X9 -> X9
 | XA -> XA
 | XB -> XB
 | XC -> XC
 | XD -> XD
 | XE -> XE
 | XF -> XF)

 | X1 -> 
(match e2 with 
   X0 -> X1
 | X1 -> X1
 | X2 -> X3
 | X3 -> X3
 | X4 -> X5
 | X5 -> X5
 | X6 -> X7
 | X7 -> X7
 | X8 -> X9
 | X9 -> X9
 | XA -> XB
 | XB -> XB
 | XC -> XD
 | XD -> XD
 | XE -> XF
 | XF -> XF)

 | X2 -> 
(match e2 with 
   X0 -> X2
 | X1 -> X3
 | X2 -> X2
 | X3 -> X3
 | X4 -> X6
 | X5 -> X7
 | X6 -> X6
 | X7 -> X7
 | X8 -> XA
 | X9 -> XB
 | XA -> XA
 | XB -> XB
 | XC -> XE
 | XD -> XF
 | XE -> XE
 | XF -> XF)

 | X3 -> 
(match e2 with 
   X0 -> X3
 | X1 -> X3
 | X2 -> X3
 | X3 -> X3
 | X4 -> X7
 | X5 -> X7
 | X6 -> X7
 | X7 -> X7
 | X8 -> XB
 | X9 -> XB
 | XA -> XB
 | XB -> XB
 | XC -> XF
 | XD -> XF
 | XE -> XF
 | XF -> XF)

 | X4 -> 
(match e2 with 
   X0 -> X4
 | X1 -> X5
 | X2 -> X6
 | X3 -> X7
 | X4 -> X4
 | X5 -> X5
 | X6 -> X6
 | X7 -> X7
 | X8 -> XC
 | X9 -> XD
 | XA -> XE
 | XB -> XF
 | XC -> XC
 | XD -> XD
 | XE -> XE
 | XF -> XF)

 | X5 -> 
(match e2 with 
   X0 -> X5
 | X1 -> X5
 | X2 -> X7
 | X3 -> X7
 | X4 -> X5
 | X5 -> X5
 | X6 -> X7
 | X7 -> X7
 | X8 -> XD
 | X9 -> XD
 | XA -> XF
 | XB -> XF
 | XC -> XD
 | XD -> XD
 | XE -> XF
 | XF -> XF)

 | X6 -> 
(match e2 with 
   X0 -> X6
 | X1 -> X7
 | X2 -> X6
 | X3 -> X7
 | X4 -> X6
 | X5 -> X7
 | X6 -> X6
 | X7 -> X7
 | X8 -> XE
 | X9 -> XF
 | XA -> XE
 | XB -> XF
 | XC -> XE
 | XD -> XF
 | XE -> XE
 | XF -> XF)

 | X7 -> 
(match e2 with 
   X0 -> X7
 | X1 -> X7
 | X2 -> X7
 | X3 -> X7
 | X4 -> X7
 | X5 -> X7
 | X6 -> X7
 | X7 -> X7
 | X8 -> XF
 | X9 -> XF
 | XA -> XF
 | XB -> XF
 | XC -> XF
 | XD -> XF
 | XE -> XF
 | XF -> XF)

 | X8 -> 
(match e2 with 
   X0 -> X8
 | X1 -> X9
 | X2 -> XA
 | X3 -> XB
 | X4 -> XC
 | X5 -> XD
 | X6 -> XE
 | X7 -> XF
 | X8 -> X8
 | X9 -> X9
 | XA -> XA
 | XB -> XB
 | XC -> XC
 | XD -> XD
 | XE -> XE
 | XF -> XF)

 | X9 -> 
(match e2 with 
   X0 -> X9
 | X1 -> X9
 | X2 -> XB
 | X3 -> XB
 | X4 -> XD
 | X5 -> XD
 | X6 -> XF
 | X7 -> XF
 | X8 -> X9
 | X9 -> X9
 | XA -> XB
 | XB -> XB
 | XC -> XD
 | XD -> XD
 | XE -> XF
 | XF -> XF)

 | XA -> 
(match e2 with 
   X0 -> XA
 | X1 -> XB
 | X2 -> XA
 | X3 -> XB
 | X4 -> XE
 | X5 -> XF
 | X6 -> XE
 | X7 -> XF
 | X8 -> XA
 | X9 -> XB
 | XA -> XA
 | XB -> XB
 | XC -> XE
 | XD -> XF
 | XE -> XE
 | XF -> XF)

 | XB -> 
(match e2 with 
   X0 -> XB
 | X1 -> XB
 | X2 -> XB
 | X3 -> XB
 | X4 -> XF
 | X5 -> XF
 | X6 -> XF
 | X7 -> XF
 | X8 -> XB
 | X9 -> XB
 | XA -> XB
 | XB -> XB
 | XC -> XF
 | XD -> XF
 | XE -> XF
 | XF -> XF)

 | XC -> 
(match e2 with 
   X0 -> XC
 | X1 -> XD
 | X2 -> XE
 | X3 -> XF
 | X4 -> XC
 | X5 -> XD
 | X6 -> XE
 | X7 -> XF
 | X8 -> XC
 | X9 -> XD
 | XA -> XE
 | XB -> XF
 | XC -> XC
 | XD -> XD
 | XE -> XE
 | XF -> XF)

 | XD -> 
(match e2 with 
   X0 -> XD
 | X1 -> XD
 | X2 -> XF
 | X3 -> XF
 | X4 -> XD
 | X5 -> XD
 | X6 -> XF
 | X7 -> XF
 | X8 -> XD
 | X9 -> XD
 | XA -> XF
 | XB -> XF
 | XC -> XD
 | XD -> XD
 | XE -> XF
 | XF -> XF)

 | XE -> 
(match e2 with 
   X0 -> XE
 | X1 -> XF
 | X2 -> XE
 | X3 -> XF
 | X4 -> XE
 | X5 -> XF
 | X6 -> XE
 | X7 -> XF
 | X8 -> XE
 | X9 -> XF
 | XA -> XE
 | XB -> XF
 | XC -> XE
 | XD -> XF
 | XE -> XE
 | XF -> XF)

 | XF -> 
(match e2 with 
   X0 -> XF
 | X1 -> XF
 | X2 -> XF
 | X3 -> XF
 | X4 -> XF
 | X5 -> XF
 | X6 -> XF
 | X7 -> XF
 | X8 -> XF
 | X9 -> XF
 | XA -> XF
 | XB -> XF
 | XC -> XF
 | XD -> XF
 | XE -> XF
 | XF -> XF)
)
))
;;

let xor_ex =
(function e1 -> (function e2 -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> X0
 | X1 -> X1
 | X2 -> X2
 | X3 -> X3
 | X4 -> X4
 | X5 -> X5
 | X6 -> X6
 | X7 -> X7
 | X8 -> X8
 | X9 -> X9
 | XA -> XA
 | XB -> XB
 | XC -> XC
 | XD -> XD
 | XE -> XE
 | XF -> XF)

 | X1 -> 
(match e2 with 
   X0 -> X1
 | X1 -> X0
 | X2 -> X3
 | X3 -> X2
 | X4 -> X5
 | X5 -> X4
 | X6 -> X7
 | X7 -> X6
 | X8 -> X9
 | X9 -> X8
 | XA -> XB
 | XB -> XA
 | XC -> XD
 | XD -> XC
 | XE -> XF
 | XF -> XE)

 | X2 -> 
(match e2 with 
   X0 -> X2
 | X1 -> X3
 | X2 -> X0
 | X3 -> X1
 | X4 -> X6
 | X5 -> X7
 | X6 -> X4
 | X7 -> X5
 | X8 -> XA
 | X9 -> XB
 | XA -> X8
 | XB -> X9
 | XC -> XE
 | XD -> XF
 | XE -> XC
 | XF -> XD)

 | X3 -> 
(match e2 with 
   X0 -> X3
 | X1 -> X2
 | X2 -> X1
 | X3 -> X0
 | X4 -> X7
 | X5 -> X6
 | X6 -> X5
 | X7 -> X4
 | X8 -> XB
 | X9 -> XA
 | XA -> X9
 | XB -> X8
 | XC -> XF
 | XD -> XE
 | XE -> XD
 | XF -> XC)

 | X4 -> 
(match e2 with 
   X0 -> X4
 | X1 -> X5
 | X2 -> X6
 | X3 -> X7
 | X4 -> X0
 | X5 -> X1
 | X6 -> X2
 | X7 -> X3
 | X8 -> XC
 | X9 -> XD
 | XA -> XE
 | XB -> XF
 | XC -> X8
 | XD -> X9
 | XE -> XA
 | XF -> XB)

 | X5 -> 
(match e2 with 
   X0 -> X5
 | X1 -> X4
 | X2 -> X7
 | X3 -> X6
 | X4 -> X1
 | X5 -> X0
 | X6 -> X3
 | X7 -> X2
 | X8 -> XD
 | X9 -> XC
 | XA -> XF
 | XB -> XE
 | XC -> X9
 | XD -> X8
 | XE -> XB
 | XF -> XA)

 | X6 -> 
(match e2 with 
   X0 -> X6
 | X1 -> X7
 | X2 -> X4
 | X3 -> X5
 | X4 -> X2
 | X5 -> X3
 | X6 -> X0
 | X7 -> X1
 | X8 -> XE
 | X9 -> XF
 | XA -> XC
 | XB -> XD
 | XC -> XA
 | XD -> XB
 | XE -> X8
 | XF -> X9)

 | X7 -> 
(match e2 with 
   X0 -> X7
 | X1 -> X6
 | X2 -> X5
 | X3 -> X4
 | X4 -> X3
 | X5 -> X2
 | X6 -> X1
 | X7 -> X0
 | X8 -> XF
 | X9 -> XE
 | XA -> XD
 | XB -> XC
 | XC -> XB
 | XD -> XA
 | XE -> X9
 | XF -> X8)

 | X8 -> 
(match e2 with 
   X0 -> X8
 | X1 -> X9
 | X2 -> XA
 | X3 -> XB
 | X4 -> XC
 | X5 -> XD
 | X6 -> XE
 | X7 -> XF
 | X8 -> X0
 | X9 -> X1
 | XA -> X2
 | XB -> X3
 | XC -> X4
 | XD -> X5
 | XE -> X6
 | XF -> X7)

 | X9 -> 
(match e2 with 
   X0 -> X9
 | X1 -> X8
 | X2 -> XB
 | X3 -> XA
 | X4 -> XD
 | X5 -> XC
 | X6 -> XF
 | X7 -> XE
 | X8 -> X1
 | X9 -> X0
 | XA -> X3
 | XB -> X2
 | XC -> X5
 | XD -> X4
 | XE -> X7
 | XF -> X6)

 | XA -> 
(match e2 with 
   X0 -> XA
 | X1 -> XB
 | X2 -> X8
 | X3 -> X9
 | X4 -> XE
 | X5 -> XF
 | X6 -> XC
 | X7 -> XD
 | X8 -> X2
 | X9 -> X3
 | XA -> X0
 | XB -> X1
 | XC -> X6
 | XD -> X7
 | XE -> X4
 | XF -> X5)

 | XB -> 
(match e2 with 
   X0 -> XB
 | X1 -> XA
 | X2 -> X9
 | X3 -> X8
 | X4 -> XF
 | X5 -> XE
 | X6 -> XD
 | X7 -> XC
 | X8 -> X3
 | X9 -> X2
 | XA -> X1
 | XB -> X0
 | XC -> X7
 | XD -> X6
 | XE -> X5
 | XF -> X4)

 | XC -> 
(match e2 with 
   X0 -> XC
 | X1 -> XD
 | X2 -> XE
 | X3 -> XF
 | X4 -> X8
 | X5 -> X9
 | X6 -> XA
 | X7 -> XB
 | X8 -> X4
 | X9 -> X5
 | XA -> X6
 | XB -> X7
 | XC -> X0
 | XD -> X1
 | XE -> X2
 | XF -> X3)

 | XD -> 
(match e2 with 
   X0 -> XD
 | X1 -> XC
 | X2 -> XF
 | X3 -> XE
 | X4 -> X9
 | X5 -> X8
 | X6 -> XB
 | X7 -> XA
 | X8 -> X5
 | X9 -> X4
 | XA -> X7
 | XB -> X6
 | XC -> X1
 | XD -> X0
 | XE -> X3
 | XF -> X2)

 | XE -> 
(match e2 with 
   X0 -> XE
 | X1 -> XF
 | X2 -> XC
 | X3 -> XD
 | X4 -> XA
 | X5 -> XB
 | X6 -> X8
 | X7 -> X9
 | X8 -> X6
 | X9 -> X7
 | XA -> X4
 | XB -> X5
 | XC -> X2
 | XD -> X3
 | XE -> X0
 | XF -> X1)

 | XF -> 
(match e2 with 
   X0 -> XF
 | X1 -> XE
 | X2 -> XD
 | X3 -> XC
 | X4 -> XB
 | X5 -> XA
 | X6 -> X9
 | X7 -> X8
 | X8 -> X7
 | X9 -> X6
 | XA -> X5
 | XB -> X4
 | XC -> X3
 | XD -> X2
 | XE -> X1
 | XF -> X0)
)
))
;;

let rcr_ex =
(function e -> (function c -> 
(match c with 
   Matita_datatypes_bool.True -> 
(match e with 
   X0 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | X2 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XF -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.True)))

 | Matita_datatypes_bool.False -> 
(match e with 
   X0 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X2 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | XF -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True)))
)
))
;;

let shr_ex =
(function e -> 
(match e with 
   X0 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X2 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | XF -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True)))
)
;;

let ror_ex =
(function e -> 
(match e with 
   X0 -> X0
 | X1 -> X8
 | X2 -> X1
 | X3 -> X9
 | X4 -> X2
 | X5 -> XA
 | X6 -> X3
 | X7 -> XB
 | X8 -> X4
 | X9 -> XC
 | XA -> X5
 | XB -> XD
 | XC -> X6
 | XD -> XE
 | XE -> X7
 | XF -> XF)
)
;;

let ror_ex_n =
let rec ror_ex_n = 
(function e -> (function n -> 
(match n with 
   Matita_nat_nat.O -> e
 | Matita_nat_nat.S(n') -> (ror_ex_n (ror_ex e) n'))
)) in ror_ex_n
;;

let rcl_ex =
(function e -> (function c -> 
(match c with 
   Matita_datatypes_bool.True -> 
(match e with 
   X0 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.True)))

 | Matita_datatypes_bool.False -> 
(match e with 
   X0 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.True)))
)
))
;;

let shl_ex =
(function e -> 
(match e with 
   X0 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.True)))
)
;;

let rol_ex =
(function e -> 
(match e with 
   X0 -> X0
 | X1 -> X2
 | X2 -> X4
 | X3 -> X6
 | X4 -> X8
 | X5 -> XA
 | X6 -> XC
 | X7 -> XE
 | X8 -> X1
 | X9 -> X3
 | XA -> X5
 | XB -> X7
 | XC -> X9
 | XD -> XB
 | XE -> XD
 | XF -> XF)
)
;;

let rol_ex_n =
let rec rol_ex_n = 
(function e -> (function n -> 
(match n with 
   Matita_nat_nat.O -> e
 | Matita_nat_nat.S(n') -> (rol_ex_n (rol_ex e) n'))
)) in rol_ex_n
;;

let not_ex =
(function e -> 
(match e with 
   X0 -> XF
 | X1 -> XE
 | X2 -> XD
 | X3 -> XC
 | X4 -> XB
 | X5 -> XA
 | X6 -> X9
 | X7 -> X8
 | X8 -> X7
 | X9 -> X6
 | XA -> X5
 | XB -> X4
 | XC -> X3
 | XD -> X2
 | XE -> X1
 | XF -> X0)
)
;;

let plus_ex =
(function e1 -> (function e2 -> (function c -> 
(match c with 
   Matita_datatypes_bool.True -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XE -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XF -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True)))

 | X1 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XE -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True)))

 | X2 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True)))

 | X3 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True)))

 | X4 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True)))

 | X5 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True)))

 | X6 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True)))

 | X7 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True)))

 | X8 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True)))

 | X9 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True)))

 | XA -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True)))

 | XB -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True)))

 | XC -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True)))

 | XD -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X3 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True)))

 | XE -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X2 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X3 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.True)))

 | XF -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X1 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X2 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X3 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.True)))
)

 | Matita_datatypes_bool.False -> 
(match e1 with 
   X0 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XE -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XF -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False)))

 | X1 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XE -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XF -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True)))

 | X2 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XE -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True)))

 | X3 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XD -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True)))

 | X4 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XC -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True)))

 | X5 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XB -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True)))

 | X6 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | XA -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True)))

 | X7 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X9 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True)))

 | X8 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X8 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True)))

 | X9 -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X7 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True)))

 | XA -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X6 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True)))

 | XB -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X5 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True)))

 | XC -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X4 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True)))

 | XD -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X3 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True)))

 | XE -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X2 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X3 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True)))

 | XF -> 
(match e2 with 
   X0 -> (Matita_datatypes_constructors.Pair(XF,Matita_datatypes_bool.False))
 | X1 -> (Matita_datatypes_constructors.Pair(X0,Matita_datatypes_bool.True))
 | X2 -> (Matita_datatypes_constructors.Pair(X1,Matita_datatypes_bool.True))
 | X3 -> (Matita_datatypes_constructors.Pair(X2,Matita_datatypes_bool.True))
 | X4 -> (Matita_datatypes_constructors.Pair(X3,Matita_datatypes_bool.True))
 | X5 -> (Matita_datatypes_constructors.Pair(X4,Matita_datatypes_bool.True))
 | X6 -> (Matita_datatypes_constructors.Pair(X5,Matita_datatypes_bool.True))
 | X7 -> (Matita_datatypes_constructors.Pair(X6,Matita_datatypes_bool.True))
 | X8 -> (Matita_datatypes_constructors.Pair(X7,Matita_datatypes_bool.True))
 | X9 -> (Matita_datatypes_constructors.Pair(X8,Matita_datatypes_bool.True))
 | XA -> (Matita_datatypes_constructors.Pair(X9,Matita_datatypes_bool.True))
 | XB -> (Matita_datatypes_constructors.Pair(XA,Matita_datatypes_bool.True))
 | XC -> (Matita_datatypes_constructors.Pair(XB,Matita_datatypes_bool.True))
 | XD -> (Matita_datatypes_constructors.Pair(XC,Matita_datatypes_bool.True))
 | XE -> (Matita_datatypes_constructors.Pair(XD,Matita_datatypes_bool.True))
 | XF -> (Matita_datatypes_constructors.Pair(XE,Matita_datatypes_bool.True)))
)
)
)))
;;

let plus_exnc =
(function e1 -> (function e2 -> (Matita_datatypes_constructors.fst (plus_ex e1 e2 Matita_datatypes_bool.False))))
;;

let plus_exc =
(function e1 -> (function e2 -> (Matita_datatypes_constructors.snd (plus_ex e1 e2 Matita_datatypes_bool.False))))
;;

let mSB_ex =
(function e -> 
(match e with 
   X0 -> Matita_datatypes_bool.False
 | X1 -> Matita_datatypes_bool.False
 | X2 -> Matita_datatypes_bool.False
 | X3 -> Matita_datatypes_bool.False
 | X4 -> Matita_datatypes_bool.False
 | X5 -> Matita_datatypes_bool.False
 | X6 -> Matita_datatypes_bool.False
 | X7 -> Matita_datatypes_bool.False
 | X8 -> Matita_datatypes_bool.True
 | X9 -> Matita_datatypes_bool.True
 | XA -> Matita_datatypes_bool.True
 | XB -> Matita_datatypes_bool.True
 | XC -> Matita_datatypes_bool.True
 | XD -> Matita_datatypes_bool.True
 | XE -> Matita_datatypes_bool.True
 | XF -> Matita_datatypes_bool.True)
)
;;

let nat_of_exadecim =
(function e -> 
(match e with 
   X0 -> Matita_nat_nat.O
 | X1 -> (Matita_nat_nat.S(Matita_nat_nat.O))
 | X2 -> (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))
 | X3 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))
 | X4 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))
 | X5 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))
 | X6 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))
 | X7 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))
 | X8 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))
 | X9 -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))
 | XA -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))))
 | XB -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))))))
 | XC -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))))))))
 | XD -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))))))))))
 | XE -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))))))))))))
 | XF -> (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))
)
;;

let exadecim_of_nat =
let rec exadecim_of_nat = 
(function n -> 
(match n with 
   Matita_nat_nat.O -> X0
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X1
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X2
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X3
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X4
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X5
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X6
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X7
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X8
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> X9
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> XA
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> XB
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> XC
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> XD
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> XE
 | Matita_nat_nat.S(n) -> 
(match n with 
   Matita_nat_nat.O -> XF
 | Matita_nat_nat.S(n) -> (exadecim_of_nat n))
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
) in exadecim_of_nat
;;

let pred_ex =
(function e -> 
(match e with 
   X0 -> XF
 | X1 -> X0
 | X2 -> X1
 | X3 -> X2
 | X4 -> X3
 | X5 -> X4
 | X6 -> X5
 | X7 -> X6
 | X8 -> X7
 | X9 -> X8
 | XA -> X9
 | XB -> XA
 | XC -> XB
 | XD -> XC
 | XE -> XD
 | XF -> XE)
)
;;

let succ_ex =
(function e -> 
(match e with 
   X0 -> X1
 | X1 -> X2
 | X2 -> X3
 | X3 -> X4
 | X4 -> X5
 | X5 -> X6
 | X6 -> X7
 | X7 -> X8
 | X8 -> X9
 | X9 -> XA
 | XA -> XB
 | XB -> XC
 | XC -> XD
 | XD -> XE
 | XE -> XF
 | XF -> X0)
)
;;

let compl_ex =
(function e -> 
(match e with 
   X0 -> X0
 | X1 -> XF
 | X2 -> XE
 | X3 -> XD
 | X4 -> XC
 | X5 -> XB
 | X6 -> XA
 | X7 -> X9
 | X8 -> X8
 | X9 -> X7
 | XA -> X6
 | XB -> X5
 | XC -> X4
 | XD -> X3
 | XE -> X2
 | XF -> X1)
)
;;

let forall_exadecim =
(function p -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (p X0) (p X1)) (p X2)) (p X3)) (p X4)) (p X5)) (p X6)) (p X7)) (p X8)) (p X9)) (p XA)) (p XB)) (p XC)) (p XD)) (p XE)) (p XF)))
;;

