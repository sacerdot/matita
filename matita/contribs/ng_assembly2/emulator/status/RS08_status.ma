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

include "emulator/status/RS08_status_base.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

nlemma aluRS08_destruct_1 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x1 = y1.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 a _ _ _ _ _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_2 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x2 = y2.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ a _ _ _ _ _ _ ⇒ x2 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_3 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x3 = y3.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ _ a _ _ _ _ _ ⇒ x3 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_4 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x4 = y4.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ _ _ a _ _ _ _ ⇒ x4 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_5 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x5 = y5.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ _ _ _ a _ _ _ ⇒ x5 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_6 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x6 = y6.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ _ _ _ _ a _ _ ⇒ x6 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_7 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x7 = y7.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ _ _ _ _ _ a _ ⇒ x7 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma aluRS08_destruct_8 :
∀x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8.
 mk_alu_RS08 x1 x2 x3 x4 x5 x6 x7 x8 = mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8 →
 x8 = y8.
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange with (match mk_alu_RS08 y1 y2 y3 y4 y5 y6 y7 y8
                with [ mk_alu_RS08 _ _ _ _ _ _ _ a ⇒ x8 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma eq_to_eqaluRS08 : ∀alu1,alu2.alu1 = alu2 → eq_RS08_alu alu1 alu2 = true.
 #alu1; #alu2;
 ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nrewrite > (aluRS08_destruct_1 … H);
 nrewrite > (aluRS08_destruct_2 … H);
 nrewrite > (aluRS08_destruct_3 … H);
 nrewrite > (aluRS08_destruct_4 … H);
 nrewrite > (aluRS08_destruct_5 … H);
 nrewrite > (aluRS08_destruct_6 … H);
 nrewrite > (aluRS08_destruct_7 … H);
 nrewrite > (aluRS08_destruct_8 … H);
 nchange with (
  ((eqc ? y1 y1) ⊗ (eqc ? y2 y2) ⊗
   (eqc ? y3 y3) ⊗ (eqc ? y4 y4) ⊗
   (eqc ? y5 y5) ⊗ (eqc ? y6 y6) ⊗
   (eqc ? y7 y7) ⊗ (eqc ? y8 y8)) = true);
 nrewrite > (eq_to_eqc ? y1 y1 (refl_eq …));
 nrewrite > (eq_to_eqc ? y2 y2 (refl_eq …));
 nrewrite > (eq_to_eqc ? y3 y3 (refl_eq …));
 nrewrite > (eq_to_eqc ? y4 y4 (refl_eq …));
 nrewrite > (eq_to_eqc ? y5 y5 (refl_eq …));
 nrewrite > (eq_to_eqc ? y6 y6 (refl_eq …));
 nrewrite > (eq_to_eqc ? y7 y7 (refl_eq …));
 nrewrite > (eq_to_eqc ? y8 y8 (refl_eq …));
 napply refl_eq.
nqed.

nlemma neqaluRS08_to_neq : ∀alu1,alu2.eq_RS08_alu alu1 alu2 = false → alu1 ≠ alu2.
 #s1; #s2; #H;
 napply (not_to_not (s1 = s2) (eq_RS08_alu s1 s2 = true) …);
 ##[ ##1: napply (eq_to_eqaluRS08 s1 s2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqaluRS08_to_eq : ∀alu1,alu2.eq_RS08_alu alu1 alu2 = true → alu1 = alu2.
 #alu1; #alu2;
 ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8; #H;
 nchange in H:(%) with (
  ((eqc ? x1 y1) ⊗ (eqc ? x2 y2) ⊗
   (eqc ? x3 y3) ⊗ (eqc ? x4 y4) ⊗
   (eqc ? x5 y5) ⊗ (eqc ? x6 y6) ⊗
   (eqc ? x7 y7) ⊗ (eqc ? x8 y8)) = true);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H));
 nletin H1 ≝ (andb_true_true_l … H);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H1));
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
 nrewrite > (eqc_to_eq … (andb_true_true_l … H6));
 napply refl_eq.
nqed.

nlemma neq_to_neqaluRS08 : ∀alu1,alu2.alu1 ≠ alu2 → eq_RS08_alu alu1 alu2 = false.
 #s1; #s2; #H;
 napply (neqtrue_to_eqfalse (eq_RS08_alu s1 s2));
 napply (not_to_not (eq_RS08_alu s1 s2 = true) (s1 = s2) ? H);
 napply (eqaluRS08_to_eq s1 s2).
nqed.

nlemma decidable_aluRS08 : ∀x,y:alu_RS08.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_RS08_alu x y = true) (eq_RS08_alu x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqaluRS08_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqaluRS08_to_neq … H))
 ##]
nqed.


nlemma symmetric_eqaluRS08 : symmetricT alu_RS08 bool eq_RS08_alu.
 #alu1; #alu2;
 ncases alu1;
 #x1; #x2; #x3; #x4; #x5; #x6; #x7; #x8;
 ncases alu2;
 #y1; #y2; #y3; #y4; #y5; #y6; #y7; #y8;
 nchange with (
  ((eqc ? x1 y1) ⊗ (eqc ? x2 y2) ⊗
   (eqc ? x3 y3) ⊗ (eqc ? x4 y4) ⊗
   (eqc ? x5 y5) ⊗ (eqc ? x6 y6) ⊗
   (eqc ? x7 y7) ⊗ (eqc ? x8 y8)) =
  ((eqc ? y1 x1) ⊗ (eqc ? y2 x2) ⊗
   (eqc ? y3 x3) ⊗ (eqc ? y4 x4) ⊗
   (eqc ? y5 x5) ⊗ (eqc ? y6 x6) ⊗
   (eqc ? y7 x7) ⊗ (eqc ? y8 x8)));
 nrewrite > (symmetric_eqc ? x1 y1);
 nrewrite > (symmetric_eqc ? x2 y2);
 nrewrite > (symmetric_eqc ? x3 y3);
 nrewrite > (symmetric_eqc ? x4 y4);
 nrewrite > (symmetric_eqc ? x5 y5);
 nrewrite > (symmetric_eqc ? x6 y6);
 nrewrite > (symmetric_eqc ? x7 y7);
 nrewrite > (symmetric_eqc ? x8 y8);
 napply refl_eq.
nqed.

nlemma aluRS08_is_comparable : comparable.
 @ alu_RS08
  ##[ napply (mk_alu_RS08 (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?)
                          (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?))
  ##| napply forall_RS08_alu
  ##| napply eq_RS08_alu
  ##| napply eqaluRS08_to_eq
  ##| napply eq_to_eqaluRS08
  ##| napply neqaluRS08_to_neq
  ##| napply neq_to_neqaluRS08
  ##| napply decidable_aluRS08
  ##| napply symmetric_eqaluRS08
  ##]
nqed.

unification hint 0 ≔ ⊢ carr aluRS08_is_comparable ≡ alu_RS08.
