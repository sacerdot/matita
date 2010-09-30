(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

universe constraint Type[0] < Type[1].
universe constraint Type[1] < Type[2].
universe constraint Type[2] < Type[3].
universe constraint Type[3] < Type[4].

(* ********************************** *)
(* SOTTOINSIEME MINIMALE DELLA TEORIA *)
(* ********************************** *)

(* logic/connectives.ma *)

ninductive True: Prop ≝
 I : True.

ninductive False: Prop ≝.

ndefinition Not: Prop → Prop ≝
λA.(A → False).

interpretation "logical not" 'not x = (Not x).

nlemma absurd : ∀A,C:Prop.A → ¬A → C.
 #A; #C; #H;
 nnormalize;
 #H1;
 nelim (H1 H).
nqed.

nlemma not_to_not : ∀A,B:Prop. (A → B) → ((¬B) → (¬A)).
 #A; #B; #H;
 nnormalize;
 #H1; #H2;
 nelim (H1 (H H2)).
nqed.

nlemma prop_to_nnprop : ∀P.P → ¬¬P.
 #P; nnormalize; #H; #H1;
 napply (H1 H).
nqed.

ninductive And2 (A,B:Prop) : Prop ≝
 conj2 : A → B → (And2 A B).

interpretation "logical and" 'and x y = (And2 x y).

nlemma proj2_1: ∀A,B:Prop.A ∧ B → A.
 #A; #B; #H;
 napply (And2_ind A B … H);
 #H1; #H2;
 napply H1.
nqed.

nlemma proj2_2: ∀A,B:Prop.A ∧ B → B.
 #A; #B; #H;
 napply (And2_ind A B … H);
 #H1; #H2;
 napply H2.
nqed.

ninductive And3 (A,B,C:Prop) : Prop ≝
 conj3 : A → B → C → (And3 A B C).

nlemma proj3_1: ∀A,B,C:Prop.And3 A B C → A.
 #A; #B; #C; #H;
 napply (And3_ind A B C … H);
 #H1; #H2; #H3;
 napply H1.
nqed.

nlemma proj3_2: ∀A,B,C:Prop.And3 A B C → B.
 #A; #B; #C; #H;
 napply (And3_ind A B C … H);
 #H1; #H2; #H3;
 napply H2.
nqed.

nlemma proj3_3: ∀A,B,C:Prop.And3 A B C → C.
 #A; #B; #C; #H;
 napply (And3_ind A B C … H);
 #H1; #H2; #H3;
 napply H3.
nqed.

ninductive And4 (A,B,C,D:Prop) : Prop ≝
 conj4 : A → B → C → D → (And4 A B C D).

nlemma proj4_1: ∀A,B,C,D:Prop.And4 A B C D → A.
 #A; #B; #C; #D; #H;
 napply (And4_ind A B C D … H);
 #H1; #H2; #H3; #H4;
 napply H1.
nqed.

nlemma proj4_2: ∀A,B,C,D:Prop.And4 A B C D → B.
 #A; #B; #C; #D; #H;
 napply (And4_ind A B C D … H);
 #H1; #H2; #H3; #H4;
 napply H2.
nqed.

nlemma proj4_3: ∀A,B,C,D:Prop.And4 A B C D → C.
 #A; #B; #C; #D; #H;
 napply (And4_ind A B C D … H);
 #H1; #H2; #H3; #H4;
 napply H3.
nqed.

nlemma proj4_4: ∀A,B,C,D:Prop.And4 A B C D → D.
 #A; #B; #C; #D; #H;
 napply (And4_ind A B C D … H);
 #H1; #H2; #H3; #H4;
 napply H4.
nqed.

ninductive And5 (A,B,C,D,E:Prop) : Prop ≝
 conj5 : A → B → C → D → E → (And5 A B C D E).

nlemma proj5_1: ∀A,B,C,D,E:Prop.And5 A B C D E → A.
 #A; #B; #C; #D; #E; #H;
 napply (And5_ind A B C D E … H);
 #H1; #H2; #H3; #H4; #H5;
 napply H1.
nqed.

nlemma proj5_2: ∀A,B,C,D,E:Prop.And5 A B C D E → B.
 #A; #B; #C; #D; #E; #H;
 napply (And5_ind A B C D E … H);
 #H1; #H2; #H3; #H4; #H5;
 napply H2.
nqed.

nlemma proj5_3: ∀A,B,C,D,E:Prop.And5 A B C D E → C.
 #A; #B; #C; #D; #E; #H;
 napply (And5_ind A B C D E … H);
 #H1; #H2; #H3; #H4; #H5;
 napply H3.
nqed.

nlemma proj5_4: ∀A,B,C,D,E:Prop.And5 A B C D E → D.
 #A; #B; #C; #D; #E; #H;
 napply (And5_ind A B C D E … H);
 #H1; #H2; #H3; #H4; #H5;
 napply H4.
nqed.

nlemma proj5_5: ∀A,B,C,D,E:Prop.And5 A B C D E → E.
 #A; #B; #C; #D; #E; #H;
 napply (And5_ind A B C D E … H);
 #H1; #H2; #H3; #H4; #H5;
 napply H5.
nqed.

ninductive Or2 (A,B:Prop) : Prop ≝
  or2_intro1 : A → (Or2 A B)
| or2_intro2 : B → (Or2 A B).

interpretation "logical or" 'or x y = (Or2 x y).

ndefinition decidable ≝ λA:Prop.A ∨ (¬A).

nlemma or2_elim
 : ∀P1,P2,Q:Prop.Or2 P1 P2 → ∀f1:P1 → Q.∀f2:P2 → Q.Q.
 #P1; #P2; #Q; #H; #f1; #f2;
 napply (Or2_ind P1 P2 ? f1 f2 ?);
 napply H.
nqed.

nlemma symmetric_or2 : ∀P1,P2.Or2 P1 P2 → Or2 P2 P1.
 #P1; #P2; #H;
 napply (or2_elim P1 P2 ? H);
 ##[ ##1: #H1; napply (or2_intro2 P2 P1 H1)
 ##| ##2: #H1; napply (or2_intro1 P2 P1 H1)
 ##]
nqed.

ninductive Or3 (A,B,C:Prop) : Prop ≝
  or3_intro1 : A → (Or3 A B C)
| or3_intro2 : B → (Or3 A B C)
| or3_intro3 : C → (Or3 A B C).

nlemma or3_elim
 : ∀P1,P2,P3,Q:Prop.Or3 P1 P2 P3 → ∀f1:P1 → Q.∀f2:P2 → Q.∀f3:P3 → Q.Q.
 #P1; #P2; #P3; #Q; #H; #f1; #f2; #f3;
 napply (Or3_ind P1 P2 P3 ? f1 f2 f3 ?);
 napply H.
nqed.

nlemma symmetric_or3_12 : ∀P1,P2,P3:Prop.Or3 P1 P2 P3 → Or3 P2 P1 P3.
 #P1; #P2; #P3; #H;
 napply (or3_elim P1 P2 P3 ? H);
 ##[ ##1: #H1; napply (or3_intro2 P2 P1 P3 H1)
 ##| ##2: #H1; napply (or3_intro1 P2 P1 P3 H1)
 ##| ##3: #H1; napply (or3_intro3 P2 P1 P3 H1)
 ##]
nqed.

nlemma symmetric_or3_13 : ∀P1,P2,P3:Prop.Or3 P1 P2 P3 → Or3 P3 P2 P1.
 #P1; #P2; #P3; #H;
 napply (or3_elim P1 P2 P3 ? H);
 ##[ ##1: #H1; napply (or3_intro3 P3 P2 P1 H1)
 ##| ##2: #H1; napply (or3_intro2 P3 P2 P1 H1)
 ##| ##3: #H1; napply (or3_intro1 P3 P2 P1 H1)
 ##]
nqed.

nlemma symmetric_or3_23 : ∀P1,P2,P3:Prop.Or3 P1 P2 P3 → Or3 P1 P3 P2.
 #P1; #P2; #P3; #H;
 napply (or3_elim P1 P2 P3 ? H);
 ##[ ##1: #H1; napply (or3_intro1 P1 P3 P2 H1)
 ##| ##2: #H1; napply (or3_intro3 P1 P3 P2 H1)
 ##| ##3: #H1; napply (or3_intro2 P1 P3 P2 H1)
 ##]
nqed.

ninductive Or4 (A,B,C,D:Prop) : Prop ≝
  or4_intro1 : A → (Or4 A B C D)
| or4_intro2 : B → (Or4 A B C D)
| or4_intro3 : C → (Or4 A B C D)
| or4_intro4 : D → (Or4 A B C D).

nlemma or4_elim
 : ∀P1,P2,P3,P4,Q:Prop.Or4 P1 P2 P3 P4 → ∀f1:P1 → Q.∀f2:P2 → Q.
   ∀f3:P3 → Q.∀f4:P4 → Q.Q.
 #P1; #P2; #P3; #P4; #Q; #H; #f1; #f2; #f3; #f4;
 napply (Or4_ind P1 P2 P3 P4 ? f1 f2 f3 f4 ?);
 napply H.
nqed.

nlemma symmetric_or4_12 : ∀P1,P2,P3,P4:Prop.Or4 P1 P2 P3 P4 → Or4 P2 P1 P3 P4.
 #P1; #P2; #P3; #P4; #H;
 napply (or4_elim P1 P2 P3 P4 ? H);
 ##[ ##1: #H1; napply (or4_intro2 P2 P1 P3 P4 H1)
 ##| ##2: #H1; napply (or4_intro1 P2 P1 P3 P4 H1)
 ##| ##3: #H1; napply (or4_intro3 P2 P1 P3 P4 H1)
 ##| ##4: #H1; napply (or4_intro4 P2 P1 P3 P4 H1)
 ##]
nqed.

nlemma symmetric_or4_13 : ∀P1,P2,P3,P4:Prop.Or4 P1 P2 P3 P4 → Or4 P3 P2 P1 P4.
 #P1; #P2; #P3; #P4; #H;
 napply (or4_elim P1 P2 P3 P4 ? H);
 ##[ ##1: #H1; napply (or4_intro3 P3 P2 P1 P4 H1)
 ##| ##2: #H1; napply (or4_intro2 P3 P2 P1 P4 H1)
 ##| ##3: #H1; napply (or4_intro1 P3 P2 P1 P4 H1)
 ##| ##4: #H1; napply (or4_intro4 P3 P2 P1 P4 H1)
 ##]
nqed.

nlemma symmetric_or4_14 : ∀P1,P2,P3,P4:Prop.Or4 P1 P2 P3 P4 → Or4 P4 P2 P3 P1.
 #P1; #P2; #P3; #P4; #H;
 napply (or4_elim P1 P2 P3 P4 ? H);
 ##[ ##1: #H1; napply (or4_intro4 P4 P2 P3 P1 H1)
 ##| ##2: #H1; napply (or4_intro2 P4 P2 P3 P1 H1)
 ##| ##3: #H1; napply (or4_intro3 P4 P2 P3 P1 H1)
 ##| ##4: #H1; napply (or4_intro1 P4 P2 P3 P1 H1)
 ##]
nqed.

nlemma symmetric_or4_23 : ∀P1,P2,P3,P4:Prop.Or4 P1 P2 P3 P4 → Or4 P1 P3 P2 P4.
 #P1; #P2; #P3; #P4; #H;
 napply (or4_elim P1 P2 P3 P4 ? H);
 ##[ ##1: #H1; napply (or4_intro1 P1 P3 P2 P4 H1)
 ##| ##2: #H1; napply (or4_intro3 P1 P3 P2 P4 H1)
 ##| ##3: #H1; napply (or4_intro2 P1 P3 P2 P4 H1)
 ##| ##4: #H1; napply (or4_intro4 P1 P3 P2 P4 H1)
 ##]
nqed.

nlemma symmetric_or4_24 : ∀P1,P2,P3,P4:Prop.Or4 P1 P2 P3 P4 → Or4 P1 P4 P3 P2.
 #P1; #P2; #P3; #P4; #H;
 napply (or4_elim P1 P2 P3 P4 ? H);
 ##[ ##1: #H1; napply (or4_intro1 P1 P4 P3 P2 H1)
 ##| ##2: #H1; napply (or4_intro4 P1 P4 P3 P2 H1)
 ##| ##3: #H1; napply (or4_intro3 P1 P4 P3 P2 H1)
 ##| ##4: #H1; napply (or4_intro2 P1 P4 P3 P2 H1)
 ##]
nqed.

nlemma symmetric_or4_34 : ∀P1,P2,P3,P4:Prop.Or4 P1 P2 P3 P4 → Or4 P1 P2 P4 P3.
 #P1; #P2; #P3; #P4; #H;
 napply (or4_elim P1 P2 P3 P4 ? H);
 ##[ ##1: #H1; napply (or4_intro1 P1 P2 P4 P3 H1)
 ##| ##2: #H1; napply (or4_intro2 P1 P2 P4 P3 H1)
 ##| ##3: #H1; napply (or4_intro4 P1 P2 P4 P3 H1)
 ##| ##4: #H1; napply (or4_intro3 P1 P2 P4 P3 H1)
 ##]
nqed.

ninductive Or5 (A,B,C,D,E:Prop) : Prop ≝
  or5_intro1 : A → (Or5 A B C D E)
| or5_intro2 : B → (Or5 A B C D E)
| or5_intro3 : C → (Or5 A B C D E)
| or5_intro4 : D → (Or5 A B C D E)
| or5_intro5 : E → (Or5 A B C D E).

nlemma or5_elim
 : ∀P1,P2,P3,P4,P5,Q:Prop.Or5 P1 P2 P3 P4 P5 → ∀f1:P1 → Q.∀f2:P2 → Q.
   ∀f3:P3 → Q.∀f4:P4 → Q.∀f5:P5 → Q.Q.
 #P1; #P2; #P3; #P4; #P5; #Q; #H; #f1; #f2; #f3; #f4; #f5;
 napply (Or5_ind P1 P2 P3 P4 P5 ? f1 f2 f3 f4 f5 ?);
 napply H.
nqed.

nlemma symmetric_or5_12 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P2 P1 P3 P4 P5.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro2 P2 P1 P3 P4 P5 H1)
 ##| ##2: #H1; napply (or5_intro1 P2 P1 P3 P4 P5 H1)
 ##| ##3: #H1; napply (or5_intro3 P2 P1 P3 P4 P5 H1)
 ##| ##4: #H1; napply (or5_intro4 P2 P1 P3 P4 P5 H1)
 ##| ##5: #H1; napply (or5_intro5 P2 P1 P3 P4 P5 H1)
 ##]
nqed.

nlemma symmetric_or5_13 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P3 P2 P1 P4 P5.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro3 P3 P2 P1 P4 P5 H1)
 ##| ##2: #H1; napply (or5_intro2 P3 P2 P1 P4 P5 H1)
 ##| ##3: #H1; napply (or5_intro1 P3 P2 P1 P4 P5 H1)
 ##| ##4: #H1; napply (or5_intro4 P3 P2 P1 P4 P5 H1)
 ##| ##5: #H1; napply (or5_intro5 P3 P2 P1 P4 P5 H1)
 ##]
nqed.

nlemma symmetric_or5_14 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P4 P2 P3 P1 P5.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro4 P4 P2 P3 P1 P5 H1)
 ##| ##2: #H1; napply (or5_intro2 P4 P2 P3 P1 P5 H1)
 ##| ##3: #H1; napply (or5_intro3 P4 P2 P3 P1 P5 H1)
 ##| ##4: #H1; napply (or5_intro1 P4 P2 P3 P1 P5 H1)
 ##| ##5: #H1; napply (or5_intro5 P4 P2 P3 P1 P5 H1)
 ##]
nqed.

nlemma symmetric_or5_15 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P5 P2 P3 P4 P1.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro5 P5 P2 P3 P4 P1 H1)
 ##| ##2: #H1; napply (or5_intro2 P5 P2 P3 P4 P1 H1)
 ##| ##3: #H1; napply (or5_intro3 P5 P2 P3 P4 P1 H1)
 ##| ##4: #H1; napply (or5_intro4 P5 P2 P3 P4 P1 H1)
 ##| ##5: #H1; napply (or5_intro1 P5 P2 P3 P4 P1 H1)
 ##]
nqed.

nlemma symmetric_or5_23 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P1 P3 P2 P4 P5.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro1 P1 P3 P2 P4 P5 H1)
 ##| ##2: #H1; napply (or5_intro3 P1 P3 P2 P4 P5 H1)
 ##| ##3: #H1; napply (or5_intro2 P1 P3 P2 P4 P5 H1)
 ##| ##4: #H1; napply (or5_intro4 P1 P3 P2 P4 P5 H1)
 ##| ##5: #H1; napply (or5_intro5 P1 P3 P2 P4 P5 H1)
 ##]
nqed.

nlemma symmetric_or5_24 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P1 P4 P3 P2 P5.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro1 P1 P4 P3 P2 P5 H1)
 ##| ##2: #H1; napply (or5_intro4 P1 P4 P3 P2 P5 H1)
 ##| ##3: #H1; napply (or5_intro3 P1 P4 P3 P2 P5 H1)
 ##| ##4: #H1; napply (or5_intro2 P1 P4 P3 P2 P5 H1)
 ##| ##5: #H1; napply (or5_intro5 P1 P4 P3 P2 P5 H1)
 ##]
nqed.

nlemma symmetric_or5_25 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P1 P5 P3 P4 P2.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro1 P1 P5 P3 P4 P2 H1)
 ##| ##2: #H1; napply (or5_intro5 P1 P5 P3 P4 P2 H1)
 ##| ##3: #H1; napply (or5_intro3 P1 P5 P3 P4 P2 H1)
 ##| ##4: #H1; napply (or5_intro4 P1 P5 P3 P4 P2 H1)
 ##| ##5: #H1; napply (or5_intro2 P1 P5 P3 P4 P2 H1)
 ##]
nqed.

nlemma symmetric_or5_34 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P1 P2 P4 P3 P5.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro1 P1 P2 P4 P3 P5 H1)
 ##| ##2: #H1; napply (or5_intro2 P1 P2 P4 P3 P5 H1)
 ##| ##3: #H1; napply (or5_intro4 P1 P2 P4 P3 P5 H1)
 ##| ##4: #H1; napply (or5_intro3 P1 P2 P4 P3 P5 H1)
 ##| ##5: #H1; napply (or5_intro5 P1 P2 P4 P3 P5 H1)
 ##]
nqed.

nlemma symmetric_or5_35 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P1 P2 P5 P4 P3.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro1 P1 P2 P5 P4 P3 H1)
 ##| ##2: #H1; napply (or5_intro2 P1 P2 P5 P4 P3 H1)
 ##| ##3: #H1; napply (or5_intro5 P1 P2 P5 P4 P3 H1)
 ##| ##4: #H1; napply (or5_intro4 P1 P2 P5 P4 P3 H1)
 ##| ##5: #H1; napply (or5_intro3 P1 P2 P5 P4 P3 H1)
 ##]
nqed.

nlemma symmetric_or5_45 : ∀P1,P2,P3,P4,P5:Prop.Or5 P1 P2 P3 P4 P5 → Or5 P1 P2 P3 P5 P4.
 #P1; #P2; #P3; #P4; #P5; #H;
 napply (or5_elim P1 P2 P3 P4 P5 ? H);
 ##[ ##1: #H1; napply (or5_intro1 P1 P2 P3 P5 P4 H1)
 ##| ##2: #H1; napply (or5_intro2 P1 P2 P3 P5 P4 H1)
 ##| ##3: #H1; napply (or5_intro3 P1 P2 P3 P5 P4 H1)
 ##| ##4: #H1; napply (or5_intro5 P1 P2 P3 P5 P4 H1)
 ##| ##5: #H1; napply (or5_intro4 P1 P2 P3 P5 P4 H1)
 ##]
nqed.

ninductive ex (A:Type) (Q:A → Prop) : Prop ≝
 ex_intro: ∀x:A.Q x → ex A Q.

interpretation "exists" 'exists x = (ex ? x).

ninductive ex2 (A:Type) (Q,R:A → Prop) : Prop ≝
 ex_intro2: ∀x:A.Q x → R x → ex2 A Q R.

(* higher_order_defs/relations *)

ndefinition relation : Type → Type ≝
λA.A → A → Prop. 

ndefinition reflexive : ∀A:Type.∀R:relation A.Prop ≝
λA.λR.∀x:A.R x x.

ndefinition symmetric : ∀A:Type.∀R:relation A.Prop ≝
λA.λR.∀x,y:A.R x y → R y x.

ndefinition transitive : ∀A:Type.∀R:relation A.Prop ≝
λA.λR.∀x,y,z:A.R x y → R y z → R x z.

ndefinition irreflexive : ∀A:Type.∀R:relation A.Prop ≝
λA.λR.∀x:A.¬ (R x x).

ndefinition cotransitive : ∀A:Type.∀R:relation A.Prop ≝
λA.λR.∀x,y:A.R x y → ∀z:A. R x z ∨ R z y.

ndefinition tight_apart : ∀A:Type.∀eq,ap:relation A.Prop ≝
λA.λeq,ap.∀x,y:A. (¬ (ap x y) → eq x y) ∧ (eq x y → ¬ (ap x y)).

ndefinition antisymmetric : ∀A:Type.∀R:relation A.Prop ≝
λA.λR.∀x,y:A.R x y → ¬ (R y x).

(* logic/equality.ma *)

ninductive eq (A:Type) (x:A) : A → Prop ≝
 refl_eq : eq A x x.

ndefinition refl ≝ refl_eq.

interpretation "leibnitz's equality" 'eq t x y = (eq t x y).

interpretation "leibnitz's non-equality" 'neq t x y = (Not (eq t x y)).

nlemma eq_f : ∀T1,T2:Type.∀x,y:T1.∀f:T1 → T2.x = y → (f x) = (f y).
 #T1; #T2; #x; #y; #f; #H;
 nrewrite < H;
 napply refl_eq.
nqed.

nlemma eq_f2 : ∀T1,T2,T3:Type.∀x1,y1:T1.∀x2,y2:T2.∀f:T1 → T2 → T3.x1 = y1 → x2 = y2 → f x1 x2 = f y1 y2.
 #T1; #T2; #T3; #x1; #y1; #x2; #y2; #f; #H1; #H2;
 nrewrite < H1;
 nrewrite < H2;
 napply refl_eq.
nqed.

nlemma neqf_to_neq : ∀T1,T2:Type.∀x,y:T1.∀f:T1 → T2.((f x) ≠ (f y)) → x ≠ y.
 #T1; #T2; #x; #y; #f;
 nnormalize; #H; #H1;
 napply (H (eq_f … H1)).
nqed.

nlemma symmetric_eq: ∀A:Type. symmetric A (eq A).
 #A;
 nnormalize;
 #x; #y; #H;
 nrewrite < H;
 napply refl_eq.
nqed.

nlemma eq_ind_r: ∀A:Type[0].∀x:A.∀P:A → Prop.P x → ∀y:A.y=x → P y.
 #A; #x; #P; #H; #y; #H1;
 nrewrite < (symmetric_eq … H1);
 napply H.
nqed.

ndefinition R0 ≝ λT:Type[0].λt:T.t.

ndefinition R1 ≝ eq_rect_Type0.

ndefinition R2 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type[0].
  ∀a1:T1 a0 (refl_eq ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ?? T1 a1 ? p0 = x1 → Type[0].
  ∀a2:T2 a0 (refl_eq ? a0) a1 (refl_eq ? a1).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ?? T1 a1 ? e0 = b1.
  T2 b0 e0 b1 e1.
 #T0;#a0;#T1;#a1;#T2;#a2;#b0;#e0;#b1;#e1;
 napply (eq_rect_Type0 ????? e1);
 napply (R1 ?? ? ?? e0);
 napply a2;
nqed.

ndefinition R3 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. a0=x0 → Type[0].
  ∀a1:T1 a0 (refl_eq ? a0).
  ∀T2:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0. R1 ?? T1 a1 ? p0 = x1 → Type[0].
  ∀a2:T2 a0 (refl_eq ? a0) a1 (refl_eq ? a1).
  ∀T3:∀x0:T0. ∀p0:a0=x0. ∀x1:T1 x0 p0.∀p1:R1 ?? T1 a1 ? p0 = x1.
      ∀x2:T2 x0 p0 x1 p1.R2 ???? T2 a2 x0 p0 ? p1 = x2 → Type[0].
  ∀a3:T3 a0 (refl_eq ? a0) a1 (refl_eq ? a1) a2 (refl_eq ? a2).
  ∀b0:T0.
  ∀e0:a0 = b0.
  ∀b1: T1 b0 e0.
  ∀e1:R1 ?? T1 a1 ? e0 = b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:R2 ???? T2 a2 b0 e0 ? e1 = b2.
  T3 b0 e0 b1 e1 b2 e2.
 #T0;#a0;#T1;#a1;#T2;#a2;#T3;#a3;#b0;#e0;#b1;#e1;#b2;#e2;
 napply (eq_rect_Type0 ????? e2);
 napply (R2 ?? ? ???? e0 ? e1);
 napply a3;
nqed.

ndefinition R4 :
  ∀T0:Type[0].
  ∀a0:T0.
  ∀T1:∀x0:T0. eq T0 a0 x0 → Type[0].
  ∀a1:T1 a0 (refl_eq T0 a0).
  ∀T2:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1 → Type[0].
  ∀a2:T2 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1).
  ∀T3:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.∀p1:eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1.
      ∀x2:T2 x0 p0 x1 p1.eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2 → Type[0].
  ∀a3:T3 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1) 
      a2 (refl_eq (T2 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1)) a2). 
  ∀T4:∀x0:T0. ∀p0:eq (T0 …) a0 x0. ∀x1:T1 x0 p0.∀p1:eq (T1 …) (R1 T0 a0 T1 a1 x0 p0) x1.
      ∀x2:T2 x0 p0 x1 p1.∀p2:eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 x0 p0 x1 p1) x2.
      ∀x3:T3 x0 p0 x1 p1 x2 p2.∀p3:eq (T3 …) (R3 T0 a0 T1 a1 T2 a2 T3 a3 x0 p0 x1 p1 x2 p2) x3. 
      Type[0].
  ∀a4:T4 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1) 
      a2 (refl_eq (T2 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1)) a2) 
      a3 (refl_eq (T3 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1) 
                   a2 (refl_eq (T2 a0 (refl_eq T0 a0) a1 (refl_eq (T1 a0 (refl_eq T0 a0)) a1)) a2))
                   a3).
  ∀b0:T0.
  ∀e0:eq (T0 …) a0 b0.
  ∀b1: T1 b0 e0.
  ∀e1:eq (T1 …) (R1 T0 a0 T1 a1 b0 e0) b1.
  ∀b2: T2 b0 e0 b1 e1.
  ∀e2:eq (T2 …) (R2 T0 a0 T1 a1 T2 a2 b0 e0 b1 e1) b2.
  ∀b3: T3 b0 e0 b1 e1 b2 e2.
  ∀e3:eq (T3 …) (R3 T0 a0 T1 a1 T2 a2 T3 a3 b0 e0 b1 e1 b2 e2) b3.
  T4 b0 e0 b1 e1 b2 e2 b3 e3.
 #T0;#a0;#T1;#a1;#T2;#a2;#T3;#a3;#T4;#a4;#b0;#e0;#b1;#e1;#b2;#e2;#b3;#e3;
 napply (eq_rect_Type0 ????? e3);
 napply (R3 ????????? e0 ? e1 ? e2);
 napply a4;
nqed.

nlemma symmetric_neq : ∀T:Type.∀x,y:T.x ≠ y → y ≠ x.
 #T; #x; #y;
 nnormalize;
 #H; #H1;
 nrewrite > H1 in H:(%); #H;
 napply (H (refl_eq …)).
nqed.

ndefinition relationT : Type → Type → Type ≝
λA,T:Type.A → A → T.

ndefinition symmetricT: ∀A,T:Type.∀R:relationT A T.Prop ≝
λA,T.λR.∀x,y:A.R x y = R y x.

ndefinition associative : ∀A:Type.∀R:relationT A A.Prop ≝
λA.λR.∀x,y,z:A.R (R x y) z = R x (R y z).
