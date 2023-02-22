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

include "num/word16_lemmas.ma".
include "emulator/status/HC08_status.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

nlemma aluHC08_destruct_1 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x1 = y1.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 a _ _ _ _ _ _ _ _ _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_2 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x2 = y2.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ a _ _ _ _ _ _ _ _ _ _ ⇒ x2 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_3 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x3 = y3.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ a _ _ _ _ _ _ _ _ _ ⇒ x3 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_4 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x4 = y4.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ a _ _ _ _ _ _ _ _ ⇒ x4 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_5 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x5 = y5.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ a _ _ _ _ _ _ _ ⇒ x5 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_6 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x6 = y6.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ a _ _ _ _ _ _ ⇒ x6 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_7 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x7 = y7.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ _ a _ _ _ _ _ ⇒ x7 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_8 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x8 = y8.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ _ _ a _ _ _ _ ⇒ x8 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_9 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x9 = y9.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ _ _ _ a _ _ _ ⇒ x9 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_10 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x10 = y10.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ _ _ _ _ a _ _ ⇒ x10 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_11 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x11 = y11.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ _ _ _ _ _ a _ ⇒ x11 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluHC08_destruct_12 :
∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 →
 x12 = y12.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange with (match mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
                with [ mk_alu_HC08 _ _ _ _ _ _ _ _ _ _ _ a ⇒ x12 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqaluHC08 : symmetricT alu_HC08 bool eq_HC08_alu.
 #alu1; #alu2;
 ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nchange with (
  ((eq_b8 x1 y1) ⊗ (eq_b8 x2 y2) ⊗ (eq_b8 x3 y3) ⊗ (eq_w16 x4 y4) ⊗
   (eq_w16 x5 y5) ⊗ (eq_bool x6 y6) ⊗ (eq_bool x7 y7) ⊗ (eq_bool x8 y8) ⊗
   (eq_bool x9 y9) ⊗ (eq_bool x10 y10) ⊗ (eq_bool x11 y11) ⊗ (eq_bool x12 y12)) =
   ((eq_b8 y1 x1) ⊗ (eq_b8 y2 x2) ⊗ (eq_b8 y3 x3) ⊗ (eq_w16 y4 x4) ⊗
   (eq_w16 y5 x5) ⊗ (eq_bool y6 x6) ⊗ (eq_bool y7 x7) ⊗ (eq_bool y8 x8) ⊗
   (eq_bool y9 x9) ⊗ (eq_bool y10 x10) ⊗ (eq_bool y11 x11) ⊗ (eq_bool y12 x12))); 
 nrewrite > (symmetric_eqb8 x1 y1);
 nrewrite > (symmetric_eqb8 x2 y2);
 nrewrite > (symmetric_eqb8 x3 y3);
 nrewrite > (symmetric_eqw16 x4 y4);
 nrewrite > (symmetric_eqw16 x5 y5);
 nrewrite > (symmetric_eqbool x6 y6);
 nrewrite > (symmetric_eqbool x7 y7);
 nrewrite > (symmetric_eqbool x8 y8);
 nrewrite > (symmetric_eqbool x9 y9);
 nrewrite > (symmetric_eqbool x10 y10);
 nrewrite > (symmetric_eqbool x11 y11);
 nrewrite > (symmetric_eqbool x12 y12);
 napply refl_eq.
nqed.

nlemma eqaluHC08_to_eq : ∀alu1,alu2.eq_HC08_alu alu1 alu2 = true → alu1 = alu2.
 #alu1; #alu2;
 ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nchange in H:(%) with (
 ((eq_b8 x1 y1) ⊗ (eq_b8 x2 y2) ⊗ (eq_b8 x3 y3) ⊗ (eq_w16 x4 y4) ⊗
  (eq_w16 x5 y5) ⊗ (eq_bool x6 y6) ⊗ (eq_bool x7 y7) ⊗ (eq_bool x8 y8) ⊗
  (eq_bool x9 y9) ⊗ (eq_bool x10 y10) ⊗ (eq_bool x11 y11) ⊗ (eq_bool x12 y12)) = true);  
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H));
 nletin H1 ≝ (andb_true_true_l … H);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H1));
 nletin H2 ≝ (andb_true_true_l … H1);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H2));
 nletin H3 ≝ (andb_true_true_l … H2);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H3));
 nletin H4 ≝ (andb_true_true_l … H3);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H4));
 nletin H5 ≝ (andb_true_true_l … H4);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H5));
 nletin H6 ≝ (andb_true_true_l … H5);
 nrewrite > (eqbool_to_eq … (andb_true_true_r … H6));
 nletin H7 ≝ (andb_true_true_l … H6);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H7));
 nletin H8 ≝ (andb_true_true_l … H7);
 nrewrite > (eqw16_to_eq … (andb_true_true_r … H8));
 nletin H9 ≝ (andb_true_true_l … H8);
 nrewrite > (eqb8_to_eq … (andb_true_true_r … H9));
 nletin H10 ≝ (andb_true_true_l … H9);
 nrewrite > (eqb8_to_eq … (andb_true_true_r … H10));
 nrewrite > (eqb8_to_eq … (andb_true_true_l … H10));
 napply refl_eq.
nqed.

nlemma eq_to_eqaluHC08 : ∀alu1,alu2.alu1 = alu2 → eq_HC08_alu alu1 alu2 = true.
 #alu1; #alu2;
 ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12; #H;
 nrewrite > (aluHC08_destruct_1 … H);
 nrewrite > (aluHC08_destruct_2 … H);
 nrewrite > (aluHC08_destruct_3 … H);
 nrewrite > (aluHC08_destruct_4 … H);
 nrewrite > (aluHC08_destruct_5 … H);
 nrewrite > (aluHC08_destruct_6 … H);
 nrewrite > (aluHC08_destruct_7 … H);
 nrewrite > (aluHC08_destruct_8 … H);
 nrewrite > (aluHC08_destruct_9 … H);
 nrewrite > (aluHC08_destruct_10 … H);
 nrewrite > (aluHC08_destruct_11 … H);
 nrewrite > (aluHC08_destruct_12 … H);
 nchange with (
 ((eq_b8 y1 y1) ⊗ (eq_b8 y2 y2) ⊗ (eq_b8 y3 y3) ⊗ (eq_w16 y4 y4) ⊗
  (eq_w16 y5 y5) ⊗ (eq_bool y6 y6) ⊗ (eq_bool y7 y7) ⊗ (eq_bool y8 y8) ⊗
  (eq_bool y9 y9) ⊗ (eq_bool y10 y10) ⊗ (eq_bool y11 y11) ⊗ (eq_bool y12 y12)) = true); 
 nrewrite > (eq_to_eqb8 y1 y1 (refl_eq …));
 nrewrite > (eq_to_eqb8 y2 y2 (refl_eq …));
 nrewrite > (eq_to_eqb8 y3 y3 (refl_eq …));
 nrewrite > (eq_to_eqw16 y4 y4 (refl_eq …));
 nrewrite > (eq_to_eqw16 y5 y5 (refl_eq …));
 nrewrite > (eq_to_eqbool y6 y6 (refl_eq …));
 nrewrite > (eq_to_eqbool y7 y7 (refl_eq …));
 nrewrite > (eq_to_eqbool y8 y8 (refl_eq …));
 nrewrite > (eq_to_eqbool y9 y9 (refl_eq …));
 nrewrite > (eq_to_eqbool y10 y10 (refl_eq …));
 nrewrite > (eq_to_eqbool y11 y11 (refl_eq …));
 nrewrite > (eq_to_eqbool y12 y12 (refl_eq …));
 napply refl_eq.
nqed.

nlemma decidable_aluHC08_aux1
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x1 ≠ y1) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_1 … H1)).
nqed.

nlemma decidable_aluHC08_aux2
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x2 ≠ y2) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_2 … H1)).
nqed.

nlemma decidable_aluHC08_aux3
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x3 ≠ y3) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_3 … H1)).
nqed.

nlemma decidable_aluHC08_aux4
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x4 ≠ y4) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_4 … H1)).
nqed.

nlemma decidable_aluHC08_aux5
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x5 ≠ y5) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_5 … H1)).
nqed.

nlemma decidable_aluHC08_aux6
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x6 ≠ y6) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_6 … H1)).
nqed.

nlemma decidable_aluHC08_aux7
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x7 ≠ y7) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_7 … H1)).
nqed.

nlemma decidable_aluHC08_aux8
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x8 ≠ y8) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_8 … H1)).
nqed.

nlemma decidable_aluHC08_aux9
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x9 ≠ y9) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_9 … H1)).
nqed.

nlemma decidable_aluHC08_aux10
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x10 ≠ y10) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_10 … H1)).
nqed.

nlemma decidable_aluHC08_aux11
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x11 ≠ y11) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_11 … H1)).
nqed.

nlemma decidable_aluHC08_aux12
 : ∀x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12.
 (x12 ≠ y12) →
 (mk_alu_HC08 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ≠
 (mk_alu_HC08 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12).
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize; #H; #H1;
 napply (H (aluHC08_destruct_12 … H1)).
nqed.

nlemma decidable_aluHC08 : ∀x,y:alu_HC08.decidable (x = y).
 #x; nelim x; #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8; #x9; #x10; #x11; #x12;
 #y; nelim y; #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #y9; #y10; #y11; #y12;
 nnormalize;
 napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_b8 x1 y1) …);
 ##[ ##2: #H; napply (or2_intro2 … (decidable_aluHC08_aux1 … H))
 ##| ##1: #H; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_b8 x2 y2) …);
  ##[ ##2: #H1; napply (or2_intro2 … (decidable_aluHC08_aux2 … H1))
  ##| ##1: #H1; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_b8 x3 y3) …);
   ##[ ##2: #H2; napply (or2_intro2 … (decidable_aluHC08_aux3 … H2))
   ##| ##1: #H2; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x4 y4) …);
    ##[ ##2: #H3; napply (or2_intro2 … (decidable_aluHC08_aux4 … H3))
    ##| ##1: #H3; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_w16 x5 y5) …);
     ##[ ##2: #H4; napply (or2_intro2 … (decidable_aluHC08_aux5 … H4))
     ##| ##1: #H4; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x6 y6) …);
      ##[ ##2: #H5; napply (or2_intro2 … (decidable_aluHC08_aux6 … H5))
      ##| ##1: #H5; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x7 y7) …);
       ##[ ##2: #H6; napply (or2_intro2 … (decidable_aluHC08_aux7 … H6))
       ##| ##1: #H6; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x8 y8) …);
        ##[ ##2: #H7; napply (or2_intro2 … (decidable_aluHC08_aux8 … H7))
        ##| ##1: #H7; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x9 y9) …);
         ##[ ##2: #H8; napply (or2_intro2 … (decidable_aluHC08_aux9 … H8))
         ##| ##1: #H8; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x10 y10) …);
          ##[ ##2: #H9; napply (or2_intro2 … (decidable_aluHC08_aux10 … H9))
          ##| ##1: #H9; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x11 y11) …);
           ##[ ##2: #H10; napply (or2_intro2 … (decidable_aluHC08_aux11 … H10))
           ##| ##1: #H10; napply (or2_elim (? = ?) (? ≠ ?) ? (decidable_bool x12 y12) …);
            ##[ ##2: #H11; napply (or2_intro2 … (decidable_aluHC08_aux12 … H11))
            ##| ##1: #H11; nrewrite > H; nrewrite > H1; nrewrite > H2; nrewrite > H3;
                      nrewrite > H4; nrewrite > H5; nrewrite > H6; nrewrite > H7;
                      nrewrite > H8; nrewrite > H9; nrewrite > H10; nrewrite > H11;
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
nqed.
