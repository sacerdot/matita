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

include "emulator/status/IP2022_status_base.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

nlemma aluIP2022_destruct_1 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x1 = y1.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_2 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x2 = y2.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ a _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x2 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_3 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x3 = y3.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ a _ _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x3 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_4 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x4 = y4.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ ⇒ x4 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_5 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x5 = y5.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ a _ _ _ _ _ _ _ _ _ _ _ ⇒ x5 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_6 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x6 = y6.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ a _ _ _ _ _ _ _ _ _ _ ⇒ x6 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_7 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x7 = y7.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ a _ _ _ _ _ _ _ _ _ ⇒ x7 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_8 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x8 = y8.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ a _ _ _ _ _ _ _ _ ⇒ x8 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_9 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x9 = y9.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ a _ _ _ _ _ _ _ ⇒ x9 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_10 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x10 = y10.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ a _ _ _ _ _ _ ⇒ x10 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_11 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x11 = y11.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ ⇒ x11 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_12 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x12 = y12.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ ⇒ x12 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_13 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x13 = y13.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ ⇒ x13 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_14 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x14 = y14.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ ⇒ x14 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_15 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x15 = y15.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ ⇒ x15 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluIP2022_destruct_16 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
 mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 →
 x16 = y16.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange with (match mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
                with [ mk_alu_IP2022 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ⇒ x16 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

(* !!! ci mette troppo tempo a compilare *)
naxiom eq_to_eqaluIP2022 : ∀alu1,alu2.alu1 = alu2 → eq_IP2022_alu alu1 alu2 = true.
(* #alu1; ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nrewrite > (aluIP2022_destruct_1 … H);
 nrewrite > (aluIP2022_destruct_2 … H);
 nrewrite > (aluIP2022_destruct_3 … H);
 nrewrite > (aluIP2022_destruct_4 … H);
 nrewrite > (aluIP2022_destruct_5 … H);
 nrewrite > (aluIP2022_destruct_6 … H);
 nrewrite > (aluIP2022_destruct_7 … H);
 nrewrite > (aluIP2022_destruct_8 … H);
 nrewrite > (aluIP2022_destruct_9 … H);
 nrewrite > (aluIP2022_destruct_10 … H);
 nrewrite > (aluIP2022_destruct_11 … H);
 nrewrite > (aluIP2022_destruct_12 … H);
 nrewrite > (aluIP2022_destruct_13 … H);
 nrewrite > (aluIP2022_destruct_14 … H);
 nrewrite > (aluIP2022_destruct_15 … H);
 nrewrite > (aluIP2022_destruct_16 … H);
 nchange with (
 ((eqc ? y1 y1) ⊗ (eqc ? y2 y2) ⊗ (eqc ? y3 y3) ⊗ (eqc ? y4 y4) ⊗
  (eqc ? y5 y5) ⊗ (eqc ? y6 y6) ⊗ (eqc ? y7 y7) ⊗ (eqc ? y8 y8) ⊗
  (eqc ? y9 y9) ⊗ (eqc ? y10 y10) ⊗ (eqc ? y11 y11) ⊗ (eqc ? y12 y12) ⊗
  (eqc ? y13 y13) ⊗ (eqc ? y14 y14) ⊗ (eqc ? y15 y15) ⊗ (eqc ? y16 y16)) = true); 
 nrewrite > (eq_to_eqc ? y1 y1 (refl_eq …));
 nrewrite > (eq_to_eqc ? y2 y2 (refl_eq …));
 nrewrite > (eq_to_eqc ? y3 y3 (refl_eq …));
 nrewrite > (eq_to_eqc ? y4 y4 (refl_eq …));
 nrewrite > (eq_to_eqc ? y5 y5 (refl_eq …));
 nrewrite > (eq_to_eqc ? y6 y6 (refl_eq …));
 nrewrite > (eq_to_eqc ? y7 y7 (refl_eq …));
 nrewrite > (eq_to_eqc ? y8 y8 (refl_eq …));
 nrewrite > (eq_to_eqc ? y9 y9 (refl_eq …));
 nrewrite > (eq_to_eqc ? y10 y10 (refl_eq …));
 nrewrite > (eq_to_eqc ? y11 y11 (refl_eq …));
 nrewrite > (eq_to_eqc ? y12 y12 (refl_eq …));
 nrewrite > (eq_to_eqc ? y13 y13 (refl_eq …));
 nrewrite > (eq_to_eqc ? y14 y14 (refl_eq …));
 nrewrite > (eq_to_eqc ? y15 y15 (refl_eq …));
 nrewrite > (eq_to_eqc ? y16 y16 (refl_eq …));
 napply refl_eq.
nqed.*)

nlemma neqaluIP2022_to_neq : ∀alu1,alu2.eq_IP2022_alu alu1 alu2 = false → alu1 ≠ alu2.
 #s1; #s2; #H;
 napply (not_to_not (s1 = s2) (eq_IP2022_alu s1 s2 = true) …);
 ##[ ##1: napply (eq_to_eqaluIP2022 s1 s2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqaluIP2022_to_eq : ∀alu1,alu2.eq_IP2022_alu alu1 alu2 = true → alu1 = alu2.
 #alu1; ncases alu1;
 #z1; #z2; #z3; #z4; #z5; #z6; #z7; #z8; #z9; #z10; #z11; #z12; #z13; #z14; #z15; #z16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange in H:(%) with (
 ((eqc ? z1 y1) ⊗ (eqc ? z2 y2) ⊗ (eqc ? z3 y3) ⊗ (eqc ? z4 y4) ⊗
  (eqc ? z5 y5) ⊗ (eqc ? z6 y6) ⊗ (eqc ? z7 y7) ⊗ (eqc ? z8 y8) ⊗
  (eqc ? z9 y9) ⊗ (eqc ? z10 y10) ⊗ (eqc ? z11 y11) ⊗ (eqc ? z12 y12) ⊗
  (eqc ? z13 y13) ⊗ (eqc ? z14 y14) ⊗ (eqc ? z15 y15) ⊗ (eqc ? z16 y16)) = true);  
 nrewrite > (eqc_to_eq … (andb_true_true_r … H));
 nletin H1 ≝ (andb_true_true_l … H);
 nrewrite > (eqc_to_eq … (andb_true_true_r … (andb_true_true_l … H)));
 nletin H2 ≝ (andb_true_true_l … H1);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H2));
 nletin H3 ≝ (andb_true_true_l … H2);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H3));
 nletin H4 ≝ (andb_true_true_l … H3);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H4));
 nletin H5 ≝ (andb_true_true_l … H4);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H5));
 nletin H6 ≝ (andb_true_true_l … H5);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H6));
 nletin H7 ≝ (andb_true_true_l … H6);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H7));
 nletin H8 ≝ (andb_true_true_l … H7);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H8));
 nletin H9 ≝ (andb_true_true_l … H8);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H9));
 nletin H10 ≝ (andb_true_true_l … H9);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H10));
 nletin H11 ≝ (andb_true_true_l … H10);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H11));
 nletin H12 ≝ (andb_true_true_l … H11);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H12));
 nletin H13 ≝ (andb_true_true_l … H12);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H13));
 nletin H14 ≝ (andb_true_true_l … H13);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H14));
 nrewrite > (eqc_to_eq … (andb_true_true_l … H14));
 napply refl_eq.
nqed.

nlemma neq_to_neqaluIP2022 : ∀alu1,alu2.alu1 ≠ alu2 → eq_IP2022_alu alu1 alu2 = false.
 #s1; #s2; #H;
 napply (neqtrue_to_eqfalse (eq_IP2022_alu s1 s2));
 napply (not_to_not (eq_IP2022_alu s1 s2 = true) (s1 = s2) ? H);
 napply (eqaluIP2022_to_eq s1 s2).
nqed.

nlemma decidable_aluIP2022 : ∀x,y:alu_IP2022.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_IP2022_alu x y = true) (eq_IP2022_alu x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqaluIP2022_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqaluIP2022_to_neq … H))
 ##]
nqed.

(* !!! ci mette troppo tempo a compilare *)
naxiom symmetric_eqaluIP2022 : symmetricT alu_IP2022 bool eq_IP2022_alu.
(* #alu1; ncases alu1;
 #z1; #z2; #z3; #z4; #z5; #z6; #z7; #z8; #z9; #z10; #z11; #z12; #z13; #z14; #z15; #z16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nchange with (
  ((eqc ? z1 y1) ⊗ (eqc ? z2 y2) ⊗ (eqc ? z3 y3) ⊗ (eqc ? z4 y4) ⊗
  (eqc ? z5 y5) ⊗ (eqc ? z6 y6) ⊗ (eqc ? z7 y7) ⊗ (eqc ? z8 y8) ⊗
  (eqc ? z9 y9) ⊗ (eqc ? z10 y10) ⊗ (eqc ? z11 y11) ⊗ (eqc ? z12 y12) ⊗
  (eqc ? z13 y13) ⊗ (eqc ? z14 y14) ⊗ (eqc ? z15 y15) ⊗ (eqc ? z16 y16)) =
  ((eqc ? y1 z1) ⊗ (eqc ? y2 z2) ⊗ (eqc ? y3 z3) ⊗ (eqc ? y4 z4) ⊗
  (eqc ? y5 z5) ⊗ (eqc ? y6 z6) ⊗ (eqc ? y7 z7) ⊗ (eqc ? y8 z8) ⊗
  (eqc ? y9 z9) ⊗ (eqc ? y10 z10) ⊗ (eqc ? y11 z11) ⊗ (eqc ? y12 z12) ⊗
  (eqc ? y13 z13) ⊗ (eqc ? y14 z14) ⊗ (eqc ? y15 z15) ⊗ (eqc ? y16 z16)));
 nrewrite > (symmetric_eqc ? z1 y1);
 nrewrite > (symmetric_eqc ? z2 y2);
 nrewrite > (symmetric_eqc ? z3 y3);
 nrewrite > (symmetric_eqc ? z4 y4);
 nrewrite > (symmetric_eqc ? z5 y5);
 nrewrite > (symmetric_eqc ? z6 y6);
 nrewrite > (symmetric_eqc ? z7 y7);
 nrewrite > (symmetric_eqc ? z8 y8);
 nrewrite > (symmetric_eqc ? z9 y9);
 nrewrite > (symmetric_eqc ? z10 y10);
 nrewrite > (symmetric_eqc ? z11 y11);
 nrewrite > (symmetric_eqc ? z12 y12);
 nrewrite > (symmetric_eqc ? z13 y13);
 nrewrite > (symmetric_eqc ? z14 y14);
 nrewrite > (symmetric_eqc ? z15 y15);
 nrewrite > (symmetric_eqc ? z16 y16);
 napply refl_eq.
nqed.*)

nlemma aluIP2022_is_comparable : comparable.
 @ alu_IP2022
  ##[ napply (mk_alu_IP2022 (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?)
                            (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?)
                            (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?)
                            (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?))
  ##| napply forall_IP2022_alu
  ##| napply eq_IP2022_alu
  ##| napply eqaluIP2022_to_eq
  ##| napply eq_to_eqaluIP2022
  ##| napply neqaluIP2022_to_neq
  ##| napply neq_to_neqaluIP2022
  ##| napply decidable_aluIP2022
  ##| napply symmetric_eqaluIP2022
  ##]
nqed.

unification hint 0 ≔ ⊢ carr aluIP2022_is_comparable ≡ alu_IP2022.
