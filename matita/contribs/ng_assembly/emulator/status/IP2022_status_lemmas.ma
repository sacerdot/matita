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

include "num/oct_lemmas.ma".
include "num/word16_lemmas.ma".
include "num/word24_lemmas.ma".
include "emulator/status/IP2022_status.ma".
include "emulator/memory/memory_struct_lemmas.ma".

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

naxiom symmetric_eqaluIP2022 : symmetricT alu_IP2022 bool eq_IP2022_alu.
(* !!! la compilazione avviene ma il tempo e' troppo lungo...
 #alu1; ncases alu1;
 #z1; #z2; #z3; #z4; #z5; #z6; #z7; #z8; #z9; #z10; #z11; #z12; #z13; #z14; #z15; #z16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nchange with (
  ((eq_b8 z1 y1) ⊗ (eq_b8 z2 y2) ⊗ (eq_b8 z3 y3) ⊗ (eq_ar8 ? eq_w24 z4 y4) ⊗
  (eq_ar16 ? eq_w16 z5 y5) ⊗ (eq_w16 z6 y6) ⊗ (eq_w16 z7 y7) ⊗ (eq_w16 z8 y8) ⊗
  (eq_w16 z9 y9) ⊗ (eq_w16 z10 y10) ⊗ (eq_ex z11 y11) ⊗ (eq_oct z12 y12) ⊗
  (eq_bool z13 y13) ⊗ (eq_bool z14 y14) ⊗ (eq_bool z15 y15) ⊗ (eq_bool z16 y16)) =
  ((eq_b8 y1 z1) ⊗ (eq_b8 y2 z2) ⊗ (eq_b8 y3 z3) ⊗ (eq_ar8 ? eq_w24 y4 z4) ⊗
  (eq_ar16 ? eq_w16 y5 z5) ⊗ (eq_w16 y6 z6) ⊗ (eq_w16 y7 z7) ⊗ (eq_w16 y8 z8) ⊗
  (eq_w16 y9 z9) ⊗ (eq_w16 y10 z10) ⊗ (eq_ex y11 z11) ⊗ (eq_oct y12 z12) ⊗
  (eq_bool y13 z13) ⊗ (eq_bool y14 z14) ⊗ (eq_bool y15 z15) ⊗ (eq_bool y16 z16)));
 nrewrite > (symmetric_eqb8 z1 y1);
 nrewrite > (symmetric_eqb8 z2 y2);
 nrewrite > (symmetric_eqb8 z3 y3);
 nrewrite > (symmetric_eqar8 ? eq_w24 symmetric_eqw24 z4 y4);
 nrewrite > (symmetric_eqar16 ? eq_w16 symmetric_eqw16 z5 y5);
 nrewrite > (symmetric_eqw16 z6 y6);
 nrewrite > (symmetric_eqw16 z7 y7);
 nrewrite > (symmetric_eqw16 z8 y8);
 nrewrite > (symmetric_eqw16 z9 y9);
 nrewrite > (symmetric_eqw16 z10 y10);
 nrewrite > (symmetric_eqex z11 y11);
 nrewrite > (symmetric_eqoct z12 y12);
 nrewrite > (symmetric_eqbool z13 y13);
 nrewrite > (symmetric_eqbool z14 y14);
 nrewrite > (symmetric_eqbool z15 y15);
 nrewrite > (symmetric_eqbool z16 y16);
 napply refl_eq.
nqed.
*)

nlemma eqaluIP2022_to_eq : ∀alu1,alu2.eq_IP2022_alu alu1 alu2 = true → alu1 = alu2.
 #alu1; ncases alu1;
 #z1; #z2; #z3; #z4; #z5; #z6; #z7; #z8; #z9; #z10; #z11; #z12; #z13; #z14; #z15; #z16;
 #alu2; ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16; #H;
 nchange in H:(%) with (
 ((eq_b8 z1 y1) ⊗ (eq_b8 z2 y2) ⊗ (eq_b8 z3 y3) ⊗ (eq_ar8 ? eq_w24 z4 y4) ⊗
  (eq_ar16 ? eq_w16 z5 y5) ⊗ (eq_w16 z6 y6) ⊗ (eq_w16 z7 y7) ⊗ (eq_w16 z8 y8) ⊗
  (eq_w16 z9 y9) ⊗ (eq_w16 z10 y10) ⊗ (eq_ex z11 y11) ⊗ (eq_oct z12 y12) ⊗
  (eq_bool z13 y13) ⊗ (eq_bool z14 y14) ⊗ (eq_bool z15 y15) ⊗ (eq_bool z16 y16)) = true);  
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H));
 nletin H1 ≝ (andb_true_true_l … H);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … (andb_true_true_l … H)));
 nletin H2 ≝ (andb_true_true_l … H1);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H2));
 nletin H3 ≝ (andb_true_true_l … H2);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H3));
 nletin H4 ≝ (andb_true_true_l … H3);
 nrewrite > (eqoct_to_eq … (andb_true_true_r … H4));
 nletin H5 ≝ (andb_true_true_l … H4);
 nrewrite > (eqex_to_eq … (andb_true_true_r … H5));
 nletin H6 ≝ (andb_true_true_l … H5);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H6));
 nletin H7 ≝ (andb_true_true_l … H6);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H7));
 nletin H8 ≝ (andb_true_true_l … H7);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H8));
 nletin H9 ≝ (andb_true_true_l … H8);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H9));
 nletin H10 ≝ (andb_true_true_l … H9);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H10));
 nletin H11 ≝ (andb_true_true_l … H10);
 nrewrite > (eqar16_to_eq ? eq_w16 eqw16_to_eq … (andb_true_true_r … H11));
 nletin H12 ≝ (andb_true_true_l … H11);
 nrewrite > (eqar8_to_eq ? eq_w24 eqw24_to_eq … (andb_true_true_r … H12));
 nletin H13 ≝ (andb_true_true_l … H12);
 nrewrite > (eqb8_to_eq … (andb_true_true_r … H13));
 nletin H14 ≝ (andb_true_true_l … H13);
 nrewrite > (eqb8_to_eq … (andb_true_true_r … H14));
 nrewrite > (eqb8_to_eq … (andb_true_true_l … H14));
 napply refl_eq.
nqed.

naxiom eq_to_eqaluIP2022 : ∀alu1,alu2.alu1 = alu2 → eq_IP2022_alu alu1 alu2 = true.
(* !!! la compilazione avviene ma il tempo e' troppo lungo...
 #alu1; ncases alu1;
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
 ((eq_b8 y1 y1) ⊗ (eq_b8 y2 y2) ⊗ (eq_b8 y3 y3) ⊗ (eq_ar8 ? eq_w24 y4 y4) ⊗
  (eq_ar16 ? eq_w16 y5 y5) ⊗ (eq_w16 y6 y6) ⊗ (eq_w16 y7 y7) ⊗ (eq_w16 y8 y8) ⊗
  (eq_w16 y9 y9) ⊗ (eq_w16 y10 y10) ⊗ (eq_ex y11 y11) ⊗ (eq_oct y12 y12) ⊗
  (eq_bool y13 y13) ⊗ (eq_bool y14 y14) ⊗ (eq_bool y15 y15) ⊗ (eq_bool y16 y16)) = true); 
 nrewrite > (eq_to_eqb8 y1 y1 (refl_eq …));
 nrewrite > (eq_to_eqb8 y2 y2 (refl_eq …));
 nrewrite > (eq_to_eqb8 y3 y3 (refl_eq …));
 nrewrite > (eq_to_eqar8 ? eq_w24 eq_to_eqw24 y4 y4 (refl_eq …));
 nrewrite > (eq_to_eqar16 ? eq_w16 eq_to_eqw16 y5 y5 (refl_eq …));
 nrewrite > (eq_to_eqw16 y6 y6 (refl_eq …));
 nrewrite > (eq_to_eqw16 y7 y7 (refl_eq …));
 nrewrite > (eq_to_eqw16 y8 y8 (refl_eq …));
 nrewrite > (eq_to_eqw16 y9 y9 (refl_eq …));
 nrewrite > (eq_to_eqw16 y10 y10 (refl_eq …));
 nrewrite > (eq_to_ex y11 y11 (refl_eq …));
 nrewrite > (eq_to_oct y12 y12 (refl_eq …));
 nrewrite > (eq_to_eqbool y13 y13 (refl_eq …));
 nrewrite > (eq_to_eqbool y14 y14 (refl_eq …));
 nrewrite > (eq_to_eqbool y15 y15 (refl_eq …));
 nrewrite > (eq_to_eqbool y16 y16 (refl_eq …));
 napply refl_eq.
nqed.
*)

nlemma decidable_aluIP2022_aux1
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x1 ≠ y1) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_1 … H1)).
nqed.

nlemma decidable_aluIP2022_aux2
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x2 ≠ y2) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_2 … H1)).
nqed.

nlemma decidable_aluIP2022_aux3
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x3 ≠ y3) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_3 … H1)).
nqed.

nlemma decidable_aluIP2022_aux4
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x4 ≠ y4) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_4 … H1)).
nqed.

nlemma decidable_aluIP2022_aux5
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x5 ≠ y5) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_5 … H1)).
nqed.

nlemma decidable_aluIP2022_aux6
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x6 ≠ y6) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_6 … H1)).
nqed.

nlemma decidable_aluIP2022_aux7
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x7 ≠ y7) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_7 … H1)).
nqed.

nlemma decidable_aluIP2022_aux8
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x8 ≠ y8) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_8 … H1)).
nqed.

nlemma decidable_aluIP2022_aux9
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x9 ≠ y9) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_9 … H1)).
nqed.

nlemma decidable_aluIP2022_aux10
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x10 ≠ y10) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_10 … H1)).
nqed.

nlemma decidable_aluIP2022_aux11
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x11 ≠ y11) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_11 … H1)).
nqed.

nlemma decidable_aluIP2022_aux12
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x12 ≠ y12) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_12 … H1)).
nqed.

nlemma decidable_aluIP2022_aux13
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x13 ≠ y13) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_13 … H1)).
nqed.

nlemma decidable_aluIP2022_aux14
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x14 ≠ y14) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_14 … H1)).
nqed.

nlemma decidable_aluIP2022_aux15
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x15 ≠ y15) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_15 … H1)).
nqed.

nlemma decidable_aluIP2022_aux16
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16.
 (x16 ≠ y16) →
 (mk_alu_IP2022 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) ≠
 (mk_alu_IP2022 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize; #H; #H1;
 napply (H (aluIP2022_destruct_16 … H1)).
nqed.

nlemma decidable_aluIP2022 : ∀x,y:alu_IP2022.decidable (x = y).
 #x; nelim x; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12; #x13; #x14; #x15; #x16;
 #y; nelim y; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #y13; #y14; #y15; #y16;
 nnormalize;
 napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_b8 x1 y1) …);
 ##[ ##2: #H; napply (or2_intro2 … (decidable_aluIP2022_aux1 … H))
 ##| ##1: #H; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_b8 x2 y2) …);
  ##[ ##2: #H1; napply (or2_intro2 … (decidable_aluIP2022_aux2 … H1))
  ##| ##1: #H1; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_b8 x3 y3) …);
   ##[ ##2: #H2; napply (or2_intro2 … (decidable_aluIP2022_aux3 … H2))
   ##| ##1: #H2; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_ar8 ? decidable_w24 x4 y4) …);
    ##[ ##2: #H3; napply (or2_intro2 … (decidable_aluIP2022_aux4 … H3))
    ##| ##1: #H3; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_ar16 ? decidable_w16 x5 y5) …);
     ##[ ##2: #H4; napply (or2_intro2 … (decidable_aluIP2022_aux5 … H4))
     ##| ##1: #H4; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x6 y6) …);
      ##[ ##2: #H5; napply (or2_intro2 … (decidable_aluIP2022_aux6 … H5))
      ##| ##1: #H5; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x7 y7) …);
       ##[ ##2: #H6; napply (or2_intro2 … (decidable_aluIP2022_aux7 … H6))
       ##| ##1: #H6; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x8 y8) …);
        ##[ ##2: #H7; napply (or2_intro2 … (decidable_aluIP2022_aux8 … H7))
        ##| ##1: #H7; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x9 y9) …);
         ##[ ##2: #H8; napply (or2_intro2 … (decidable_aluIP2022_aux9 … H8))
         ##| ##1: #H8; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x10 y10) …);
          ##[ ##2: #H9; napply (or2_intro2 … (decidable_aluIP2022_aux10 … H9))
          ##| ##1: #H9; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_ex x11 y11) …);
           ##[ ##2: #H10; napply (or2_intro2 … (decidable_aluIP2022_aux11 … H10))
           ##| ##1: #H10; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_oct x12 y12) …);
            ##[ ##2: #H11; napply (or2_intro2 … (decidable_aluIP2022_aux12 … H11))
            ##| ##1: #H11; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x13 y13) …);
             ##[ ##2: #H12; napply (or2_intro2 … (decidable_aluIP2022_aux13 … H12))
             ##| ##1: #H12; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x14 y14) …);
              ##[ ##2: #H13; napply (or2_intro2 … (decidable_aluIP2022_aux14 … H13))
              ##| ##1: #H13; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x15 y15) …);
               ##[ ##2: #H14; napply (or2_intro2 … (decidable_aluIP2022_aux15 … H14))
               ##| ##1: #H14; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x16 y16) …);
                ##[ ##2: #H15; napply (or2_intro2 … (decidable_aluIP2022_aux16 … H15))
                ##| ##1: #H15; nrewrite > H; nrewrite > H1; nrewrite > H2; nrewrite > H3;
                      nrewrite > H4; nrewrite > H5; nrewrite > H6; nrewrite > H7;
                      nrewrite > H8; nrewrite > H9; nrewrite > H10; nrewrite > H11;
                      nrewrite > H12; nrewrite > H13; nrewrite > H14; nrewrite > H15;
                      napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …));
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
