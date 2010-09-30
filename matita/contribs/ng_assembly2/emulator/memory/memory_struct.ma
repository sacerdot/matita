(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "emulator/memory/memory_struct_base.ma".

(* **************** *)
(* TIPO ARRAY DA 16 *)
(* **************** *)

nlemma ar16_destruct_1 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x1 = y1.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_2 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x2 = y2.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ a _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x2 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_3 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x3 = y3.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ a _ _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x3 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_4 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x4 = y4.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x4 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_5 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x5 = y5.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ a _ _ _ _ _ _ _ _ _ _ _ ⇒ x5 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_6 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x6 = y6.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ a _ _ _ _ _ _ _ _ _ _ ⇒ x6 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_7 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x7 = y7.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ a _ _ _ _ _ _ _ _ _ ⇒ x7 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_8 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x8 = y8.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ a _ _ _ _ _ _ _ _ ⇒ x8 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_9 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x9 = y9.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ a _ _ _ _ _ _ _ ⇒ x9 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_10 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x10 = y10.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ a _ _ _ _ _ _ ⇒ x10 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_11 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x11 = y11.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ ⇒ x11 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_12 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x12 = y12.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ ⇒ x12 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_13 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x13 = y13.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ ⇒ x13 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_14 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x14 = y14.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ ⇒ x14 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_15 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x15 = y15.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ ⇒ x15 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar16_destruct_16 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x16 = y16.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_Array16T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ⇒ x16 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqar16 :
∀T.∀f:T → T → bool.
 (symmetricT T bool f) →
 (symmetricT (Array16T T) bool (eq_ar16 T f)).
 #T; #f; #H;
 #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nchange with (
  ((f x1 y1) ⊗ (f x2 y2) ⊗ (f x3 y3) ⊗ (f x4 y4) ⊗
   (f x5 y5) ⊗ (f x6 y6) ⊗ (f x7 y7) ⊗ (f x8 y8) ⊗
   (f x9 y9) ⊗ (f x10 y10) ⊗ (f x11 y11) ⊗ (f x12 y12) ⊗
   (f x13 y13) ⊗ (f x14 y14) ⊗ (f x15 y15) ⊗ (f x16 y16)) =
  ((f y1 x1) ⊗ (f y2 x2) ⊗ (f y3 x3) ⊗ (f y4 x4) ⊗
   (f y5 x5) ⊗ (f y6 x6) ⊗ (f y7 x7) ⊗ (f y8 x8) ⊗
   (f y9 x9) ⊗ (f y10 x10) ⊗ (f y11 x11) ⊗ (f y12 x12) ⊗
   (f y13 x13) ⊗ (f y14 x14) ⊗ (f y15 x15) ⊗ (f y16 x16)));
 nrewrite > (H x1 y1);
 nrewrite > (H x2 y2);
 nrewrite > (H x3 y3);
 nrewrite > (H x4 y4);
 nrewrite > (H x5 y5);
 nrewrite > (H x6 y6);
 nrewrite > (H x7 y7);
 nrewrite > (H x8 y8);
 nrewrite > (H x9 y9);
 nrewrite > (H x10 y10);
 nrewrite > (H x11 y11);
 nrewrite > (H x12 y12);
 nrewrite > (H x13 y13);
 nrewrite > (H x14 y14);
 nrewrite > (H x15 y15);
 nrewrite > (H x16 y16);
 napply refl_eq.
nqed.

nlemma eqar16_to_eq :
∀T.∀f:T → T → bool.
 (∀x,y.(f x y = true) → (x = y)) →
 (∀a1,a2:Array16T T.(eq_ar16 T f a1 a2 = true) → (a1 = a2)).
 #T; #f; #H;
 #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H1;
 nchange in H1:(%) with (
  ((f x1 y1) ⊗ (f x2 y2) ⊗ (f x3 y3) ⊗ (f x4 y4) ⊗
   (f x5 y5) ⊗ (f x6 y6) ⊗ (f x7 y7) ⊗ (f x8 y8) ⊗
   (f x9 y9) ⊗ (f x10 y10) ⊗ (f x11 y11) ⊗ (f x12 y12) ⊗
   (f x13 y13) ⊗ (f x14 y14) ⊗ (f x15 y15) ⊗ (f x16 y16)) = true);
 nrewrite > (H … (andb_true_true_r … H1));
 nletin H2 ≝ (andb_true_true_l … H1);
 nrewrite > (H … (andb_true_true_r … H2));
 nletin H3 ≝ (andb_true_true_l … H2);
 nrewrite > (H … (andb_true_true_r … H3));
 nletin H4 ≝ (andb_true_true_l … H3);
 nrewrite > (H … (andb_true_true_r … H4));
 nletin H5 ≝ (andb_true_true_l … H4);
 nrewrite > (H … (andb_true_true_r … H5));
 nletin H6 ≝ (andb_true_true_l … H5);
 nrewrite > (H … (andb_true_true_r … H6));
 nletin H7 ≝ (andb_true_true_l … H6);
 nrewrite > (H … (andb_true_true_r … H7));
 nletin H8 ≝ (andb_true_true_l … H7);
 nrewrite > (H … (andb_true_true_r … H8));
 nletin H9 ≝ (andb_true_true_l … H8);
 nrewrite > (H … (andb_true_true_r … H9));
 nletin H10 ≝ (andb_true_true_l … H9);
 nrewrite > (H … (andb_true_true_r … H10));
 nletin H11 ≝ (andb_true_true_l … H10);
 nrewrite > (H … (andb_true_true_r … H11));
 nletin H12 ≝ (andb_true_true_l … H11);
 nrewrite > (H … (andb_true_true_r … H12));
 nletin H13 ≝ (andb_true_true_l … H12);
 nrewrite > (H … (andb_true_true_r … H13));
 nletin H14 ≝ (andb_true_true_l … H13);
 nrewrite > (H … (andb_true_true_r … H14));
 nletin H15 ≝ (andb_true_true_l … H14);
 nrewrite > (H … (andb_true_true_r … H15));
 nrewrite > (H … (andb_true_true_l … H15));
 napply refl_eq.
nqed.

nlemma eq_to_eqar16 :
∀T.∀f:T → T → bool.
 (∀x,y.(x = y) → (f x y = true)) →
 (∀a1,a2:Array16T T.(a1 = a2) → (eq_ar16 T f a1 a2 = true)).
 #T; #f; #H;
 #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H1;
 nrewrite > (ar16_destruct_1 … H1);
 nrewrite > (ar16_destruct_2 … H1);
 nrewrite > (ar16_destruct_3 … H1);
 nrewrite > (ar16_destruct_4 … H1);
 nrewrite > (ar16_destruct_5 … H1);
 nrewrite > (ar16_destruct_6 … H1);
 nrewrite > (ar16_destruct_7 … H1);
 nrewrite > (ar16_destruct_8 … H1);
 nrewrite > (ar16_destruct_9 … H1);
 nrewrite > (ar16_destruct_10 … H1);
 nrewrite > (ar16_destruct_11 … H1);
 nrewrite > (ar16_destruct_12 … H1);
 nrewrite > (ar16_destruct_13 … H1);
 nrewrite > (ar16_destruct_14 … H1);
 nrewrite > (ar16_destruct_15 … H1);
 nrewrite > (ar16_destruct_16 … H1);
 nchange with (
  ((f y1 y1) ⊗ (f y2 y2) ⊗ (f y3 y3) ⊗ (f y4 y4) ⊗
   (f y5 y5) ⊗ (f y6 y6) ⊗ (f y7 y7) ⊗ (f y8 y8) ⊗
   (f y9 y9) ⊗ (f y10 y10) ⊗ (f y11 y11) ⊗ (f y12 y12) ⊗
   (f y13 y13) ⊗ (f y14 y14) ⊗ (f y15 y15) ⊗ (f y16 y16)) = true);
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 napply refl_eq.
nqed.

nlemma decidable_ar16_aux1 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x1 ≠ y1) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_1 … H1)).
nqed.

nlemma decidable_ar16_aux2 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x2 ≠ y2) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_2 … H1)).
nqed.

nlemma decidable_ar16_aux3 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x3 ≠ y3) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_3 … H1)).
nqed.

nlemma decidable_ar16_aux4 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x4 ≠ y4) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_4 … H1)).
nqed.

nlemma decidable_ar16_aux5 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x5 ≠ y5) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_5 … H1)).
nqed.

nlemma decidable_ar16_aux6 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x6 ≠ y6) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_6 … H1)).
nqed.

nlemma decidable_ar16_aux7 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x7 ≠ y7) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_7 … H1)).
nqed.

nlemma decidable_ar16_aux8 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x8 ≠ y8) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_8 … H1)).
nqed.

nlemma decidable_ar16_aux9 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x9 ≠ y9) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_9 … H1)).
nqed.

nlemma decidable_ar16_aux10 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x10 ≠ y10) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_10 … H1)).
nqed.

nlemma decidable_ar16_aux11 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x11 ≠ y11) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_11 … H1)).
nqed.

nlemma decidable_ar16_aux12 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x12 ≠ y12) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_12 … H1)).
nqed.

nlemma decidable_ar16_aux13 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x13 ≠ y13) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_13 … H1)).
nqed.

nlemma decidable_ar16_aux14 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x14 ≠ y14) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_14 … H1)).
nqed.

nlemma decidable_ar16_aux15 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x15 ≠ y15) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_15 … H1)).
nqed.

nlemma decidable_ar16_aux16 :
∀T.
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16:T.
∀y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16:T.
 (x16 ≠ y16) →
 (mk_Array16T T x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_Array16T T y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (ar16_destruct_16 … H1)).
nqed.

nlemma decidable_ar16 :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀a1,a2:Array16T T.decidable (a1 = a2)).
 #T; #H;
 #x; nelim x; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y; nelim y; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize;
 napply (or2_elim (? = ?) (? ≠ ?) ? (H x1 y1) …);
 ##[ ##2: #H1; napply (or2_intro2 … (decidable_ar16_aux1 T … H1))
 ##| ##1: #H1; napply (or2_elim (? = ?) (? ≠ ?) ? (H x2 y2) …);
  ##[ ##2: #H2; napply (or2_intro2 … (decidable_ar16_aux2 T … H2))
  ##| ##1: #H2; napply (or2_elim (? = ?) (? ≠ ?) ? (H x3 y3) …);
   ##[ ##2: #H3; napply (or2_intro2 … (decidable_ar16_aux3 T … H3))
   ##| ##1: #H3; napply (or2_elim (? = ?) (? ≠ ?) ? (H x4 y4) …);
    ##[ ##2: #H4; napply (or2_intro2 … (decidable_ar16_aux4 T … H4))
    ##| ##1: #H4; napply (or2_elim (? = ?) (? ≠ ?) ? (H x5 y5) …);
     ##[ ##2: #H5; napply (or2_intro2 … (decidable_ar16_aux5 T … H5))
     ##| ##1: #H5; napply (or2_elim (? = ?) (? ≠ ?) ? (H x6 y6) …);
      ##[ ##2: #H6; napply (or2_intro2 … (decidable_ar16_aux6 T … H6))
      ##| ##1: #H6; napply (or2_elim (? = ?) (? ≠ ?) ? (H x7 y7) …);
       ##[ ##2: #H7; napply (or2_intro2 … (decidable_ar16_aux7 T … H7))
       ##| ##1: #H7; napply (or2_elim (? = ?) (? ≠ ?) ? (H x8 y8) …);
        ##[ ##2: #H8; napply (or2_intro2 … (decidable_ar16_aux8 T … H8))
        ##| ##1: #H8; napply (or2_elim (? = ?) (? ≠ ?) ? (H x9 y9) …);
         ##[ ##2: #H9; napply (or2_intro2 … (decidable_ar16_aux9 T … H9))
         ##| ##1: #H9; napply (or2_elim (? = ?) (? ≠ ?) ? (H x10 y10) …);
          ##[ ##2: #H10; napply (or2_intro2 … (decidable_ar16_aux10 T … H10))
          ##| ##1: #H10; napply (or2_elim (? = ?) (? ≠ ?) ? (H x11 y11) …);
           ##[ ##2: #H11; napply (or2_intro2 … (decidable_ar16_aux11 T … H11))
           ##| ##1: #H11; napply (or2_elim (? = ?) (? ≠ ?) ? (H x12 y12) …);
            ##[ ##2: #H12; napply (or2_intro2 … (decidable_ar16_aux12 T … H12))
            ##| ##1: #H12; napply (or2_elim (? = ?) (? ≠ ?) ? (H x13 y13) …);
             ##[ ##2: #H13; napply (or2_intro2 … (decidable_ar16_aux13 T … H13))
             ##| ##1: #H13; napply (or2_elim (? = ?) (? ≠ ?) ? (H x14 y14) …);
              ##[ ##2: #H14; napply (or2_intro2 … (decidable_ar16_aux14 T … H14))
              ##| ##1: #H14; napply (or2_elim (? = ?) (? ≠ ?) ? (H x15 y15) …);
               ##[ ##2: #H15; napply (or2_intro2 … (decidable_ar16_aux15 T … H15))
               ##| ##1: #H15; napply (or2_elim (? = ?) (? ≠ ?) ? (H x16 y16) …);
                ##[ ##2: #H16; napply (or2_intro2 … (decidable_ar16_aux16 T … H16))
                ##| ##1: #H16; nrewrite > H1; nrewrite > H2; nrewrite > H3; nrewrite > H4;
                      nrewrite > H5; nrewrite > H6; nrewrite > H7; nrewrite > H8;
                      nrewrite > H9; nrewrite > H10; nrewrite > H11; nrewrite > H12;
                      nrewrite > H13; nrewrite > H14; nrewrite > H15; nrewrite > H16;
                      napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
                ##]
               ##]
              ##]
             ##]
            ##]
           ##]
          ##]
         ##]
        ##]
       ##]
      ##]
     ##]
    ##]
   ##]
  ##]
 ##]
nqed.

(* !!! per brevita *)
naxiom neqar16_to_neq :
∀T.∀f:T → T → bool.
 (∀x,y:T.f x y = false → x ≠ y) →
 (∀p1,p2:Array16T T.(eq_ar16 T f p1 p2 = false → p1 ≠ p2)).

(* !!! per brevita *)
naxiom neq_to_neqar16 :
∀T.∀f:T → T → bool.
 (∀x,y:T.decidable (x = y)) →
 (∀x,y:T.x ≠ y → f x y = false) →
 (∀p1,p2:Array16T T.(p1 ≠ p2 → eq_ar16 T f p1 p2 = false)).

nlemma ar16_is_comparable : comparable → comparable.
 #T; @ (Array16T T)
  ##[ napply (mk_Array16T ? (zeroc T) (zeroc T) (zeroc T) (zeroc T)
                            (zeroc T) (zeroc T) (zeroc T) (zeroc T)
                            (zeroc T) (zeroc T) (zeroc T) (zeroc T)
                            (zeroc T) (zeroc T) (zeroc T) (zeroc T))
  ##| napply (λP.(forallc T)
              (λe1.(forallc T)
               (λe2.(forallc T)
                (λe3.(forallc T)
                 (λe4.(forallc T)
                  (λe5.(forallc T)
                   (λe6.(forallc T)
                    (λe7.(forallc T)
                     (λe8.(forallc T)
                      (λe9.(forallc T)
                       (λe10.(forallc T)
                        (λe11.(forallc T)
                         (λe12.(forallc T)
                          (λe13.(forallc T)
                           (λe14.(forallc T)
                            (λe15.(forallc T)
                             (λe16.P (mk_Array16T T e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16))))))))))))))))))
  ##| napply (eq_ar16 … (eqc T))
  ##| napply eqar16_to_eq;
      napply (eqc_to_eq T)
  ##| napply eq_to_eqar16;
      napply (eq_to_eqc T)
  ##| napply neqar16_to_neq;
      napply (neqc_to_neq T)
  ##| napply neq_to_neqar16;
      ##[ napply (decidable_c T)
      ##| napply (neq_to_neqc T) ##]
  ##| napply decidable_ar16;
      napply (decidable_c T)
  ##| napply symmetric_eqar16;
      napply (symmetric_eqc T)
  ##]
nqed.

unification hint 0 ≔ S: comparable ;
         T ≟ (carr S),
         X ≟ (ar16_is_comparable S)
 (*********************************************) ⊢
         carr X ≡ Array16T T.

(* *************** *)
(* TIPO ARRAY DA 8 *)
(* *************** *)

nlemma ar8_destruct_1 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x1 = y1.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T a _ _ _ _ _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_2 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x2 = y2.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ a _ _ _ _ _ _ ⇒ x2 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_3 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x3 = y3.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ _ a _ _ _ _ _ ⇒ x3 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_4 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x4 = y4.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ _ _ a _ _ _ _ ⇒ x4 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_5 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x5 = y5.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ _ _ _ a _ _ _ ⇒ x5 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_6 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x6 = y6.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ _ _ _ _ a _ _ ⇒ x6 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_7 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x7 = y7.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ _ _ _ _ _ a _ ⇒ x7 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma ar8_destruct_8 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8:T.∀y1,y2,y3,y4,y5,y6,y7,y8:T.
 mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8 = mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8  →
 x8 = y8.
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_Array8T _ _ _ _ _ _ _ a ⇒ x8 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqar8 :
∀T.∀f:T → T → bool.
 (symmetricT T bool f) →
 (symmetricT (Array8T T) bool (eq_ar8 T f)).
 #T; #f; #H;
 #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8;
 nchange with (
  ((f x1 y1) ⊗ (f x2 y2) ⊗ (f x3 y3) ⊗ (f x4 y4) ⊗
   (f x5 y5) ⊗ (f x6 y6) ⊗ (f x7 y7) ⊗ (f x8 y8)) =
  ((f y1 x1) ⊗ (f y2 x2) ⊗ (f y3 x3) ⊗ (f y4 x4) ⊗
   (f y5 x5) ⊗ (f y6 x6) ⊗ (f y7 x7) ⊗ (f y8 x8)));
 nrewrite > (H x1 y1);
 nrewrite > (H x2 y2);
 nrewrite > (H x3 y3);
 nrewrite > (H x4 y4);
 nrewrite > (H x5 y5);
 nrewrite > (H x6 y6);
 nrewrite > (H x7 y7);
 nrewrite > (H x8 y8);
 napply refl_eq.
nqed.

nlemma eqar8_to_eq :
∀T.∀f:T → T → bool.
 (∀x,y.(f x y = true) → (x = y)) →
 (∀a1,a2:Array8T T.(eq_ar8 T f a1 a2 = true) → (a1 = a2)).
 #T; #f; #H;
 #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H1;
 nchange in H1:(%) with (
  ((f x1 y1) ⊗ (f x2 y2) ⊗ (f x3 y3) ⊗ (f x4 y4) ⊗
   (f x5 y5) ⊗ (f x6 y6) ⊗ (f x7 y7) ⊗ (f x8 y8)) = true);
 nrewrite > (H … (andb_true_true_r … H1));
 nletin H2 ≝ (andb_true_true_l … H1);
 nrewrite > (H … (andb_true_true_r … H2));
 nletin H3 ≝ (andb_true_true_l … H2);
 nrewrite > (H … (andb_true_true_r … H3));
 nletin H4 ≝ (andb_true_true_l … H3);
 nrewrite > (H … (andb_true_true_r … H4));
 nletin H5 ≝ (andb_true_true_l … H4);
 nrewrite > (H … (andb_true_true_r … H5));
 nletin H6 ≝ (andb_true_true_l … H5);
 nrewrite > (H … (andb_true_true_r … H6));
 nletin H7 ≝ (andb_true_true_l … H6);
 nrewrite > (H … (andb_true_true_r … H7));
 nrewrite > (H … (andb_true_true_l … H7));
 napply refl_eq.
nqed.

nlemma eq_to_eqar8 :
∀T.∀f:T → T → bool.
 (∀x,y.(x = y) → (f x y = true)) →
 (∀a1,a2:Array8T T.(a1 = a2) → (eq_ar8 T f a1 a2 = true)).
 #T; #f; #H;
 #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H1;
 nrewrite > (ar8_destruct_1 … H1);
 nrewrite > (ar8_destruct_2 … H1);
 nrewrite > (ar8_destruct_3 … H1);
 nrewrite > (ar8_destruct_4 … H1);
 nrewrite > (ar8_destruct_5 … H1);
 nrewrite > (ar8_destruct_6 … H1);
 nrewrite > (ar8_destruct_7 … H1);
 nrewrite > (ar8_destruct_8 … H1);
 nchange with (
  ((f y1 y1) ⊗ (f y2 y2) ⊗ (f y3 y3) ⊗ (f y4 y4) ⊗
   (f y5 y5) ⊗ (f y6 y6) ⊗ (f y7 y7) ⊗ (f y8 y8)) = true);
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 nrewrite > (H … (refl_eq …));
 napply refl_eq.
nqed.

nlemma decidable_ar8_aux1 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x1 ≠ y1) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_1 … H1)).
nqed.

nlemma decidable_ar8_aux2 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x2 ≠ y2) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_2 … H1)).
nqed.

nlemma decidable_ar8_aux3 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x3 ≠ y3) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_3 … H1)).
nqed.

nlemma decidable_ar8_aux4 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x4 ≠ y4) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_4 … H1)).
nqed.

nlemma decidable_ar8_aux5 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x5 ≠ y5) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_5 … H1)).
nqed.

nlemma decidable_ar8_aux6 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x6 ≠ y6) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_6 … H1)).
nqed.

nlemma decidable_ar8_aux7 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x7 ≠ y7) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_7 … H1)).
nqed.

nlemma decidable_ar8_aux8 :
∀T.∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8:T.
 (x8 ≠ y8) →
 (mk_Array8T T x1 x2 x3 x4 x5 x6 x7 x8) ≠ (mk_Array8T T y1 y2 y3 y4 y5 y6 y7 y8).
 #T; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; 
 nnormalize; #H; #H1;
 napply (H (ar8_destruct_8 … H1)).
nqed.

nlemma decidable_ar8 :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀a1,a2:Array8T T.decidable (a1 = a2)).
 #T; #H;
 #x; nelim x; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y; nelim y; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8;
 nnormalize;
 napply (or2_elim (? = ?) (? ≠ ?) ? (H x1 y1) …);
 ##[ ##2: #H1; napply (or2_intro2 … (decidable_ar8_aux1 T … H1))
 ##| ##1: #H1; napply (or2_elim (? = ?) (? ≠ ?) ? (H x2 y2) …);
  ##[ ##2: #H2; napply (or2_intro2 … (decidable_ar8_aux2 T … H2))
  ##| ##1: #H2; napply (or2_elim (? = ?) (? ≠ ?) ? (H x3 y3) …);
   ##[ ##2: #H3; napply (or2_intro2 … (decidable_ar8_aux3 T … H3))
   ##| ##1: #H3; napply (or2_elim (? = ?) (? ≠ ?) ? (H x4 y4) …);
    ##[ ##2: #H4; napply (or2_intro2 … (decidable_ar8_aux4 T … H4))
    ##| ##1: #H4; napply (or2_elim (? = ?) (? ≠ ?) ? (H x5 y5) …);
     ##[ ##2: #H5; napply (or2_intro2 … (decidable_ar8_aux5 T … H5))
     ##| ##1: #H5; napply (or2_elim (? = ?) (? ≠ ?) ? (H x6 y6) …);
      ##[ ##2: #H6; napply (or2_intro2 … (decidable_ar8_aux6 T … H6))
      ##| ##1: #H6; napply (or2_elim (? = ?) (? ≠ ?) ? (H x7 y7) …);
       ##[ ##2: #H7; napply (or2_intro2 … (decidable_ar8_aux7 T … H7))
       ##| ##1: #H7; napply (or2_elim (? = ?) (? ≠ ?) ? (H x8 y8) …);
        ##[ ##2: #H8; napply (or2_intro2 … (decidable_ar8_aux8 T … H8))
        ##| ##1: #H8; nrewrite > H1; nrewrite > H2; nrewrite > H3; nrewrite > H4;
                      nrewrite > H5; nrewrite > H6; nrewrite > H7; nrewrite > H8;
                      napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
        ##]
       ##]
      ##]
     ##]
    ##]
   ##]
  ##]
 ##]
nqed.

(* !!! per brevita *)
naxiom neqar8_to_neq :
∀T.∀f:T → T → bool.
 (∀x,y:T.f x y = false → x ≠ y) →
 (∀p1,p2:Array8T T.(eq_ar8 T f p1 p2 = false → p1 ≠ p2)).

(* !!! per brevita *)
naxiom neq_to_neqar8 :
∀T.∀f:T → T → bool.
 (∀x,y:T.decidable (x = y)) →
 (∀x,y:T.x ≠ y → f x y = false) →
 (∀p1,p2:Array8T T.(p1 ≠ p2 → eq_ar8 T f p1 p2 = false)).

nlemma ar8_is_comparable : comparable → comparable.
 #T; @ (Array8T T)
  ##[ napply (mk_Array8T ? (zeroc T) (zeroc T) (zeroc T) (zeroc T)
                           (zeroc T) (zeroc T) (zeroc T) (zeroc T))
  ##| napply (λP.(forallc T)
              (λe1.(forallc T)
               (λe2.(forallc T)
                (λe3.(forallc T)
                 (λe4.(forallc T)
                  (λe5.(forallc T)
                   (λe6.(forallc T)
                    (λe7.(forallc T)
                     (λe8.P (mk_Array8T T e1 e2 e3 e4 e5 e6 e7 e8))))))))))
  ##| napply (eq_ar8 … (eqc T))
  ##| napply eqar8_to_eq;
      napply (eqc_to_eq T)
  ##| napply eq_to_eqar8;
      napply (eq_to_eqc T)
  ##| napply neqar8_to_neq;
      napply (neqc_to_neq T)
  ##| napply neq_to_neqar8;
      ##[ napply (decidable_c T)
      ##| napply (neq_to_neqc T) ##]
  ##| napply decidable_ar8;
      napply (decidable_c T)
  ##| napply symmetric_eqar8;
      napply (symmetric_eqc T)
  ##]
nqed.

unification hint 0 ≔ S: comparable ;
         T ≟ (carr S),
         X ≟ (ar8_is_comparable S)
 (*********************************************) ⊢
         carr X ≡ Array8T T.
