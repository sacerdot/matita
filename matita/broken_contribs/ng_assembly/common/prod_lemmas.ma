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

include "common/prod.ma".
include "num/bool_lemmas.ma".

(* ********* *)
(* TUPLE x 2 *)
(* ********* *)

nlemma pair_destruct_1 :
∀T1,T2.∀x1,x2:T1.∀y1,y2:T2.
 pair T1 T2 x1 y1 = pair T1 T2 x2 y2 → x1 = x2.
 #T1; #T2; #x1; #x2; #y1; #y2; #H;
 nchange with (match pair T1 T2 x2 y2 with [ pair a _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma pair_destruct_2 :
∀T1,T2.∀x1,x2:T1.∀y1,y2:T2.
 pair T1 T2 x1 y1 = pair T1 T2 x2 y2 → y1 = y2.
 #T1; #T2; #x1; #x2; #y1; #y2; #H;
 nchange with (match pair T1 T2 x2 y2 with [ pair _ b ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqpair :
∀T1,T2:Type.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.
 (symmetricT T1 bool f1) →
 (symmetricT T2 bool f2) →
 (∀p1,p2:ProdT T1 T2. 
  (eq_pair T1 T2 f1 f2 p1 p2 = eq_pair T1 T2 f1 f2 p1 p2)).
 #T1; #T2; #f1; #f2; #H; #H1;
 #p1; nelim p1; #x1; #y1;
 #p2; nelim p2; #x2; #y2;
 nnormalize;
 nrewrite > (H x1 x2);
 ncases (f1 x2 x1);
 nnormalize;
 ##[ ##1: nrewrite > (H1 y1 y2); napply refl_eq
 ##| ##2: napply refl_eq
 ##]
nqed.

nlemma eq_to_eqpair :
∀T1,T2.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.
 (∀x,y:T1.x = y → f1 x y = true) →
 (∀x,y:T2.x = y → f2 x y = true) →
 (∀p1,p2:ProdT T1 T2.
   (p1 = p2 → eq_pair T1 T2 f1 f2 p1 p2 = true)).
 #T1; #T2; #f1; #f2; #H1; #H2;
 #p1; nelim p1; #x1; #y1;
 #p2; nelim p2; #x2; #y2; #H;
 nnormalize;
 nrewrite > (H1 … (pair_destruct_1 … H));
 nnormalize;
 nrewrite > (H2 … (pair_destruct_2 … H));
 napply refl_eq.
nqed.

nlemma eqpair_to_eq :
∀T1,T2.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.
 (∀x,y:T1.f1 x y = true → x = y) →
 (∀x,y:T2.f2 x y = true → x = y) →
 (∀p1,p2:ProdT T1 T2. 
  (eq_pair T1 T2 f1 f2 p1 p2 = true → p1 = p2)).
 #T1; #T2; #f1; #f2; #H1; #H2;
 #p1; nelim p1; #x1; #y1;
 #p2; nelim p2; #x2; #y2; #H;
 nnormalize in H:(%);
 nletin K ≝ (H1 x1 x2);
 ncases (f1 x1 x2) in H:(%) K:(%);
 nnormalize;
 #H3;
 ##[ ##2: ndestruct (*napply (bool_destruct … H3)*) ##]
 #H4;
 nrewrite > (H4 (refl_eq …));
 nrewrite > (H2 y1 y2 H3);
 napply refl_eq.
nqed.

nlemma decidable_pair :
∀T1,T2.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:ProdT T1 T2.decidable (x = y)).
 #T1; #T2; #H; #H1;
 #x; nelim x; #xx1; #xx2;
 #y; nelim y; #yy1; #yy2;
 nnormalize;
 napply (or2_elim (xx1 = yy1) (xx1 ≠ yy1) ? (H xx1 yy1) ?);
 ##[ ##2: #H2; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
          nnormalize; #H3; napply (H2 (pair_destruct_1 T1 T2 … H3))
 ##| ##1: #H2; napply (or2_elim (xx2 = yy2) (xx2 ≠ yy2) ? (H1 xx2 yy2) ?);
          ##[ ##2: #H3; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H4; napply (H3 (pair_destruct_2 T1 T2 … H4))
          ##| ##1: #H3; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                   nrewrite > H2; nrewrite > H3; napply refl_eq
          ##]
 ##]
nqed.

nlemma neqpair_to_neq :
∀T1,T2.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.
 (∀x,y:T1.f1 x y = false → x ≠ y) →
 (∀x,y:T2.f2 x y = false → x ≠ y) →
 (∀p1,p2:ProdT T1 T2.  
  (eq_pair T1 T2 f1 f2 p1 p2 = false → p1 ≠ p2)).
 #T1; #T2; #f1; #f2; #H1; #H2;
 #p1; nelim p1; #x1; #y1;
 #p2; nelim p2; #x2; #y2;
 nchange with ((((f1 x1 x2) ⊗ (f2 y1 y2)) = false) → ?); #H;
 nnormalize; #H3;
 napply (or2_elim ((f1 x1 x2) = false) ((f2 y1 y2) = false) ? (andb_false2 … H) ?);
 ##[ ##1: #H4; napply (H1 x1 x2 H4); napply (pair_destruct_1 T1 T2 … H3)
 ##| ##2: #H4; napply (H2 y1 y2 H4); napply (pair_destruct_2 T1 T2 … H3)
 ##]
nqed.

nlemma pair_destruct :
∀T1,T2.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x1,x2:T1.∀y1,y2:T2.
  (pair T1 T2 x1 y1) ≠ (pair T1 T2 x2 y2) → x1 ≠ x2 ∨ y1 ≠ y2).
 #T1; #T2; #H1; #H2; #x1; #x2; #y1; #y2;
 nnormalize; #H;
 napply (or2_elim (x1 = x2) (x1 ≠ x2) ? (H1 x1 x2) ?);
 ##[ ##2: #H3; napply (or2_intro1 … H3)
 ##| ##1: #H3; napply (or2_elim (y1 = y2) (y1 ≠ y2) ? (H2 y1 y2) ?);
          ##[ ##2: #H4; napply (or2_intro2 … H4)
          ##| ##1: #H4; nrewrite > H3 in H:(%);
                   nrewrite > H4; #H; nelim (H (refl_eq …))
          ##]
 ##]
nqed.

nlemma neq_to_neqpair :
∀T1,T2.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T1.x ≠ y → f1 x y = false) →
 (∀x,y:T2.x ≠ y → f2 x y = false) →
 (∀p1,p2:ProdT T1 T2. 
  (p1 ≠ p2 → eq_pair T1 T2 f1 f2 p1 p2 = false)).
 #T1; #T2; #f1; #f2; #H1; #H2; #H3; #H4;
 #p1; nelim p1; #x1; #y1;
 #p2; nelim p2; #x2; #y2; #H;
 nchange with (((f1 x1 x2) ⊗ (f2 y1 y2)) = false);
 napply (or2_elim (x1 ≠ x2) (y1 ≠ y2) ? (pair_destruct T1 T2 H1 H2 … H) ?);
 ##[ ##2: #H5; nrewrite > (H4 … H5); nrewrite > (andb_false2_2 (f1 x1 x2)); napply refl_eq
 ##| ##1: #H5; nrewrite > (H3 … H5); nnormalize; napply refl_eq
 ##]
nqed.

(* ********* *)
(* TUPLE x 3 *)
(* ********* *)

nlemma triple_destruct_1 :
∀T1,T2,T3.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.
 triple T1 T2 T3 x1 y1 z1 = triple T1 T2 T3 x2 y2 z2 → x1 = x2.
 #T1; #T2; #T3; #x1; #x2; #y1; #y2; #z1; #z2; #H;
 nchange with (match triple T1 T2 T3 x2 y2 z2 with [ triple a _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma triple_destruct_2 :
∀T1,T2,T3.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.
 triple T1 T2 T3 x1 y1 z1 = triple T1 T2 T3 x2 y2 z2 → y1 = y2.
 #T1; #T2; #T3; #x1; #x2; #y1; #y2; #z1; #z2; #H;
 nchange with (match triple T1 T2 T3 x2 y2 z2 with [ triple _ b _ ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma triple_destruct_3 :
∀T1,T2,T3.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.
 triple T1 T2 T3 x1 y1 z1 = triple T1 T2 T3 x2 y2 z2 → z1 = z2.
 #T1; #T2; #T3; #x1; #x2; #y1; #y2; #z1; #z2; #H;
 nchange with (match triple T1 T2 T3 x2 y2 z2 with [ triple _ _ c ⇒ z1 = c ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqtriple :
∀T1,T2,T3:Type.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.
 (symmetricT T1 bool f1) →
 (symmetricT T2 bool f2) →
 (symmetricT T3 bool f3) →
 (∀p1,p2:Prod3T T1 T2 T3.
  (eq_triple T1 T2 T3 f1 f2 f3 p1 p2 = eq_triple T1 T2 T3 f1 f2 f3 p2 p1)).
 #T1; #T2; #T3; #f1; #f2; #f3; #H; #H1; #H2;
 #p1; nelim p1; #x1; #y1; #z1;
 #p2; nelim p2; #x2; #y2; #z2;
 nnormalize;
 nrewrite > (H x1 x2);
 ncases (f1 x2 x1);
 nnormalize;
 ##[ ##1: nrewrite > (H1 y1 y2);
          ncases (f2 y2 y1);
          nnormalize;
          ##[ ##1: nrewrite > (H2 z1 z2); napply refl_eq
          ##| ##2: napply refl_eq
          ##]
 ##| ##2: napply refl_eq
 ##]
nqed.

nlemma eq_to_eqtriple :
∀T1,T2,T3.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.
 (∀x1,x2:T1.x1 = x2 → f1 x1 x2 = true) →
 (∀y1,y2:T2.y1 = y2 → f2 y1 y2 = true) →
 (∀z1,z2:T3.z1 = z2 → f3 z1 z2 = true) →
 (∀p1,p2:Prod3T T1 T2 T3.
  (p1 = p2 → eq_triple T1 T2 T3 f1 f2 f3 p1 p2 = true)).
 #T1; #T2; #T3; #f1; #f2; #f3; #H1; #H2; #H3;
 #p1; nelim p1; #x1; #y1; #z1;
 #p2; nelim p2; #x2; #y2; #z2; #H;
 nnormalize;
 nrewrite > (H1 … (triple_destruct_1 … H));
 nnormalize;
 nrewrite > (H2 … (triple_destruct_2 … H));
 nnormalize;
 nrewrite > (H3 … (triple_destruct_3 … H));
 napply refl_eq.
nqed.

nlemma eqtriple_to_eq :
∀T1,T2,T3.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.
 (∀x1,x2:T1.f1 x1 x2 = true → x1 = x2) →
 (∀y1,y2:T2.f2 y1 y2 = true → y1 = y2) →
 (∀z1,z2:T3.f3 z1 z2 = true → z1 = z2) →
 (∀p1,p2:Prod3T T1 T2 T3.
  (eq_triple T1 T2 T3 f1 f2 f3 p1 p2 = true → p1 = p2)).
 #T1; #T2; #T3; #f1; #f2; #f3; #H1; #H2; #H3;
 #p1; nelim p1; #x1; #y1; #z1;
 #p2; nelim p2; #x2; #y2; #z2; #H;
 nnormalize in H:(%);
 nletin K ≝ (H1 x1 x2);
 ncases (f1 x1 x2) in H:(%) K:(%);
 nnormalize;
 ##[ ##2: #H4; ndestruct (*napply (bool_destruct … H4)*) ##]
 nletin K1 ≝ (H2 y1 y2);
 ncases (f2 y1 y2) in K1:(%) ⊢ %;
 nnormalize;
 ##[ ##2: #H4; #H5; ndestruct (*napply (bool_destruct … H5)*) ##]
 #H4; #H5; #H6;
 nrewrite > (H4 (refl_eq …));
 nrewrite > (H6 (refl_eq …));
 nrewrite > (H3 z1 z2 H5);
 napply refl_eq.
nqed.

nlemma decidable_triple :
∀T1,T2,T3.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:Prod3T T1 T2 T3.decidable (x = y)).
 #T1; #T2; #T3; #H; #H1; #H2;
 #x; nelim x; #xx1; #xx2; #xx3;
 #y; nelim y; #yy1; #yy2; #yy3;
 nnormalize;
 napply (or2_elim (xx1 = yy1) (xx1 ≠ yy1) ? (H xx1 yy1) ?);
 ##[ ##2: #H3; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
          nnormalize; #H4; napply (H3 (triple_destruct_1 T1 T2 T3 … H4))
 ##| ##1: #H3; napply (or2_elim (xx2 = yy2) (xx2 ≠ yy2) ? (H1 xx2 yy2) ?);
          ##[ ##2: #H4; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H5; napply (H4 (triple_destruct_2 T1 T2 T3 … H5))
          ##| ##1: #H4; napply (or2_elim (xx3 = yy3) (xx3 ≠ yy3) ? (H2 xx3 yy3) ?);
                   ##[ ##2: #H5; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H6; napply (H5 (triple_destruct_3 T1 T2 T3 … H6))
                   ##| ##1: #H5; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                            nrewrite > H3;
                            nrewrite > H4;
                            nrewrite > H5;
                            napply refl_eq
                   ##]
          ##]
 ##]
nqed.

nlemma neqtriple_to_neq :
∀T1,T2,T3.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.
 (∀x,y:T1.f1 x y = false → x ≠ y) →
 (∀x,y:T2.f2 x y = false → x ≠ y) →
 (∀x,y:T3.f3 x y = false → x ≠ y) →
 (∀p1,p2:Prod3T T1 T2 T3. 
  (eq_triple T1 T2 T3 f1 f2 f3 p1 p2 = false → p1 ≠ p2)).
 #T1; #T2; #T3; #f1; #f2; #f3; #H1; #H2; #H3;
 #p1; nelim p1; #x1; #y1; #z1;
 #p2; nelim p2; #x2; #y2; #z2;
 nchange with ((((f1 x1 x2) ⊗ (f2 y1 y2) ⊗ (f3 z1 z2)) = false) → ?); #H;
 nnormalize; #H4;
 napply (or3_elim ((f1 x1 x2) = false) ((f2 y1 y2) = false) ((f3 z1 z2) = false) ? (andb_false3 … H) ?);
 ##[ ##1: #H5; napply (H1 x1 x2 H5); napply (triple_destruct_1 T1 T2 T3 … H4)
 ##| ##2: #H5; napply (H2 y1 y2 H5); napply (triple_destruct_2 T1 T2 T3 … H4)
 ##| ##3: #H5; napply (H3 z1 z2 H5); napply (triple_destruct_3 T1 T2 T3 … H4)
 ##]
nqed.

nlemma triple_destruct :
∀T1,T2,T3.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.
  (triple T1 T2 T3 x1 y1 z1) ≠ (triple T1 T2 T3 x2 y2 z2) →
  Or3 (x1 ≠ x2) (y1 ≠ y2) (z1 ≠ z2)).
 #T1; #T2; #T3; #H1; #H2; #H3; #x1; #x2; #y1; #y2; #z1; #z2;
 nnormalize; #H;
 napply (or2_elim (x1 = x2) (x1 ≠ x2) ? (H1 x1 x2) ?);
 ##[ ##2: #H4; napply (or3_intro1 … H4)
 ##| ##1: #H4; napply (or2_elim (y1 = y2) (y1 ≠ y2) ? (H2 y1 y2) ?);
          ##[ ##2: #H5; napply (or3_intro2 … H5)
          ##| ##1: #H5; napply (or2_elim (z1 = z2) (z1 ≠ z2) ? (H3 z1 z2) ?);
                   ##[ ##2: #H6; napply (or3_intro3 … H6)
                   ##| ##1: #H6; nrewrite > H4 in H:(%);
                            nrewrite > H5;
                            nrewrite > H6; #H; nelim (H (refl_eq …))
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_neqtriple :
∀T1,T2,T3.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T1.x ≠ y → f1 x y = false) →
 (∀x,y:T2.x ≠ y → f2 x y = false) →
 (∀x,y:T3.x ≠ y → f3 x y = false) →
 (∀p1,p2:Prod3T T1 T2 T3. 
  (p1 ≠ p2 → eq_triple T1 T2 T3 f1 f2 f3 p1 p2 = false)).
 #T1; #T2; #T3; #f1; #f2; #f3; #H1; #H2; #H3; #H4; #H5; #H6;
 #p1; nelim p1; #x1; #y1; #z1;
 #p2; nelim p2; #x2; #y2; #z2; #H;
 nchange with (((f1 x1 x2) ⊗ (f2 y1 y2) ⊗ (f3 z1 z2)) = false);
 napply (or3_elim (x1 ≠ x2) (y1 ≠ y2) (z1 ≠ z2) ? (triple_destruct T1 T2 T3 H1 H2 H3 … H) ?);
 ##[ ##1: #H7; nrewrite > (H4 … H7); nrewrite > (andb_false3_1 (f2 y1 y2) (f3 z1 z2)); napply refl_eq
 ##| ##2: #H7; nrewrite > (H5 … H7); nrewrite > (andb_false3_2 (f1 x1 x2) (f3 z1 z2)); napply refl_eq
 ##| ##3: #H7; nrewrite > (H6 … H7); nrewrite > (andb_false3_3 (f1 x1 x2) (f2 y1 y2)); napply refl_eq
 ##]
nqed.

(* ********* *)
(* TUPLE x 4 *)
(* ********* *)

nlemma quadruple_destruct_1 :
∀T1,T2,T3,T4.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.
 quadruple T1 T2 T3 T4 x1 y1 z1 v1 = quadruple T1 T2 T3 T4 x2 y2 z2 v2 → x1 = x2.
 #T1; #T2; #T3; #T4; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #H;
 nchange with (match quadruple T1 T2 T3 T4 x2 y2 z2 v2 with [ quadruple a _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quadruple_destruct_2 :
∀T1,T2,T3,T4.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.
 quadruple T1 T2 T3 T4 x1 y1 z1 v1 = quadruple T1 T2 T3 T4 x2 y2 z2 v2 → y1 = y2.
 #T1; #T2; #T3; #T4; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #H;
 nchange with (match quadruple T1 T2 T3 T4 x2 y2 z2 v2 with [ quadruple _ b _ _ ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quadruple_destruct_3 :
∀T1,T2,T3,T4.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.
 quadruple T1 T2 T3 T4 x1 y1 z1 v1 = quadruple T1 T2 T3 T4 x2 y2 z2 v2 → z1 = z2.
 #T1; #T2; #T3; #T4; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #H;
 nchange with (match quadruple T1 T2 T3 T4 x2 y2 z2 v2 with [ quadruple _ _ c _ ⇒ z1 = c ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quadruple_destruct_4 :
∀T1,T2,T3,T4.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.
 quadruple T1 T2 T3 T4 x1 y1 z1 v1 = quadruple T1 T2 T3 T4 x2 y2 z2 v2 → v1 = v2.
 #T1; #T2; #T3; #T4; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #H;
 nchange with (match quadruple T1 T2 T3 T4 x2 y2 z2 v2 with [ quadruple _ _ _ d ⇒ v1 = d ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqquadruple :
∀T1,T2,T3,T4:Type.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.
 (symmetricT T1 bool f1) →
 (symmetricT T2 bool f2) →
 (symmetricT T3 bool f3) →
 (symmetricT T4 bool f4) →
 (∀p1,p2:Prod4T T1 T2 T3 T4.
  (eq_quadruple T1 T2 T3 T4 f1 f2 f3 f4 p1 p2 = eq_quadruple T1 T2 T3 T4 f1 f2 f3 f4 p2 p1)).
 #T1; #T2; #T3; #T4; #f1; #f2; #f3; #f4; #H; #H1; #H2; #H3;
 #p1; nelim p1; #x1; #y1; #z1; #v1;
 #p2; nelim p2; #x2; #y2; #z2; #v2;
 nnormalize;
 nrewrite > (H x1 x2);
 ncases (f1 x2 x1);
 nnormalize;
 ##[ ##1: nrewrite > (H1 y1 y2);
          ncases (f2 y2 y1);
          nnormalize;
          ##[ ##1: nrewrite > (H2 z1 z2);
                   ncases (f3 z2 z1);
                   nnormalize;
                   ##[ ##1: nrewrite > (H3 v1 v2); napply refl_eq
                   ##| ##2: napply refl_eq
                   ##]
          ##| ##2: napply refl_eq
          ##]
 ##| ##2: napply refl_eq
 ##]
nqed.

nlemma eq_to_eqquadruple :
∀T1,T2,T3,T4.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.
 (∀x,y:T1.x = y → f1 x y = true) →
 (∀x,y:T2.x = y → f2 x y = true) →
 (∀x,y:T3.x = y → f3 x y = true) →
 (∀x,y:T4.x = y → f4 x y = true) →
 (∀p1,p2:Prod4T T1 T2 T3 T4.
  (p1 = p2 → eq_quadruple T1 T2 T3 T4 f1 f2 f3 f4 p1 p2 = true)).
 #T1; #T2; #T3; #T4; #f1; #f2; #f3; #f4; #H1; #H2; #H3; #H4;
 #p1; nelim p1; #x1; #y1; #z1; #v1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #H;
 nnormalize;
 nrewrite > (H1 … (quadruple_destruct_1 … H));
 nnormalize;
 nrewrite > (H2 … (quadruple_destruct_2 … H));
 nnormalize;
 nrewrite > (H3 … (quadruple_destruct_3 … H));
 nnormalize;
 nrewrite > (H4 … (quadruple_destruct_4 … H));
 napply refl_eq.
nqed.

nlemma eqquadruple_to_eq :
∀T1,T2,T3,T4.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.
 (∀x,y:T1.f1 x y = true → x = y) →
 (∀x,y:T2.f2 x y = true → x = y) →
 (∀x,y:T3.f3 x y = true → x = y) →
 (∀x,y:T4.f4 x y = true → x = y) →
 (∀p1,p2:Prod4T T1 T2 T3 T4.
  (eq_quadruple T1 T2 T3 T4 f1 f2 f3 f4 p1 p2 = true → p1 = p2)).
 #T1; #T2; #T3; #T4; #f1; #f2; #f3; #f4; #H1; #H2; #H3; #H4;
 #p1; nelim p1; #x1; #y1; #z1; #v1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #H;
 nnormalize in H:(%);
 nletin K ≝ (H1 x1 x2);
 ncases (f1 x1 x2) in H:(%) K:(%);
 nnormalize;
 ##[ ##2: #H5; ndestruct (*napply (bool_destruct … H5)*) ##]
 nletin K1 ≝ (H2 y1 y2);
 ncases (f2 y1 y2) in K1:(%) ⊢ %;
 nnormalize;
 ##[ ##2: #H5; #H6; ndestruct (*napply (bool_destruct … H6)*) ##]
 nletin K2 ≝ (H3 z1 z2);
 ncases (f3 z1 z2) in K2:(%) ⊢ %;
 nnormalize;
 ##[ ##2: #H5; #H6; #H7; ndestruct (*napply (bool_destruct … H7)*) ##]
 #H5; #H6; #H7; #H8;
 nrewrite > (H5 (refl_eq …));
 nrewrite > (H6 (refl_eq …));
 nrewrite > (H8 (refl_eq …));
 nrewrite > (H4 v1 v2 H7);
 napply refl_eq.
nqed.

nlemma decidable_quadruple :
∀T1,T2,T3,T4.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T4.decidable (x = y)) →
 (∀x,y:Prod4T T1 T2 T3 T4.decidable (x = y)).
 #T1; #T2; #T3; #T4; #H; #H1; #H2; #H3;
 #x; nelim x; #xx1; #xx2; #xx3; #xx4;
 #y; nelim y; #yy1; #yy2; #yy3; #yy4;
 nnormalize;
 napply (or2_elim (xx1 = yy1) (xx1 ≠ yy1) ? (H xx1 yy1) ?);
 ##[ ##2: #H4; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
          nnormalize; #H5; napply (H4 (quadruple_destruct_1 T1 T2 T3 T4 … H5))
 ##| ##1: #H4; napply (or2_elim (xx2 = yy2) (xx2 ≠ yy2) ? (H1 xx2 yy2) ?);
          ##[ ##2: #H5; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H6; napply (H5 (quadruple_destruct_2 T1 T2 T3 T4 … H6))
          ##| ##1: #H5; napply (or2_elim (xx3 = yy3) (xx3 ≠ yy3) ? (H2 xx3 yy3) ?);
                   ##[ ##2: #H6; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H7; napply (H6 (quadruple_destruct_3 T1 T2 T3 T4 … H7))
                   ##| ##1: #H6; napply (or2_elim (xx4 = yy4) (xx4 ≠ yy4) ? (H3 xx4 yy4) ?);
                            ##[ ##2: #H7; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                     nnormalize; #H8; napply (H7 (quadruple_destruct_4 T1 T2 T3 T4 … H8))
                            ##| ##1: #H7; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                                     nrewrite > H4;
                                     nrewrite > H5;
                                     nrewrite > H6;
                                     nrewrite > H7;
                                     napply refl_eq
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma neqquadruple_to_neq :
∀T1,T2,T3,T4.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.
 (∀x,y:T1.f1 x y = false → x ≠ y) →
 (∀x,y:T2.f2 x y = false → x ≠ y) →
 (∀x,y:T3.f3 x y = false → x ≠ y) →
 (∀x,y:T4.f4 x y = false → x ≠ y) →
 (∀p1,p2:Prod4T T1 T2 T3 T4. 
  (eq_quadruple T1 T2 T3 T4 f1 f2 f3 f4 p1 p2 = false → p1 ≠ p2)).
 #T1; #T2; #T3; #T4; #f1; #f2; #f3; #f4; #H1; #H2; #H3; #H4;
 #p1; nelim p1; #x1; #y1; #z1; #v1;
 #p2; nelim p2; #x2; #y2; #z2; #v2;
 nchange with ((((f1 x1 x2) ⊗ (f2 y1 y2) ⊗ (f3 z1 z2) ⊗ (f4 v1 v2)) = false) → ?); #H;
 nnormalize; #H5;
 napply (or4_elim ((f1 x1 x2) = false) ((f2 y1 y2) = false) ((f3 z1 z2) = false) ((f4 v1 v2) = false) ? (andb_false4 … H) ?);
 ##[ ##1: #H6; napply (H1 x1 x2 H6); napply (quadruple_destruct_1 T1 T2 T3 T4 … H5)
 ##| ##2: #H6; napply (H2 y1 y2 H6); napply (quadruple_destruct_2 T1 T2 T3 T4 … H5)
 ##| ##3: #H6; napply (H3 z1 z2 H6); napply (quadruple_destruct_3 T1 T2 T3 T4 … H5)
 ##| ##4: #H6; napply (H4 v1 v2 H6); napply (quadruple_destruct_4 T1 T2 T3 T4 … H5)
 ##]
nqed.

nlemma quadruple_destruct :
∀T1,T2,T3,T4.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T4.decidable (x = y)) →
 (∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.
  (quadruple T1 T2 T3 T4 x1 y1 z1 v1) ≠ (quadruple T1 T2 T3 T4 x2 y2 z2 v2) →
  Or4 (x1 ≠ x2) (y1 ≠ y2) (z1 ≠ z2) (v1 ≠ v2)).
 #T1; #T2; #T3; #T4; #H1; #H2; #H3; #H4;
 #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2;
 nnormalize; #H;
 napply (or2_elim (x1 = x2) (x1 ≠ x2) ? (H1 x1 x2) ?);
 ##[ ##2: #H5; napply (or4_intro1 … H5)
 ##| ##1: #H5; napply (or2_elim (y1 = y2) (y1 ≠ y2) ? (H2 y1 y2) ?);
          ##[ ##2: #H6; napply (or4_intro2 … H6)
          ##| ##1: #H6; napply (or2_elim (z1 = z2) (z1 ≠ z2) ? (H3 z1 z2) ?);
                   ##[ ##2: #H7; napply (or4_intro3 … H7)
                   ##| ##1: #H7; napply (or2_elim (v1 = v2) (v1 ≠ v2) ? (H4 v1 v2) ?);
                            ##[ ##2: #H8; napply (or4_intro4 … H8)
                            ##| ##1: #H8; nrewrite > H5 in H:(%);
                                     nrewrite > H6;
                                     nrewrite > H7;
                                     nrewrite > H8; #H; nelim (H (refl_eq …))
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_neqquadruple :
∀T1,T2,T3,T4.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T4.decidable (x = y)) →
 (∀x,y:T1.x ≠ y → f1 x y = false) →
 (∀x,y:T2.x ≠ y → f2 x y = false) →
 (∀x,y:T3.x ≠ y → f3 x y = false) →
 (∀x,y:T4.x ≠ y → f4 x y = false) →
 (∀p1,p2:Prod4T T1 T2 T3 T4. 
  (p1 ≠ p2 → eq_quadruple T1 T2 T3 T4 f1 f2 f3 f4 p1 p2 = false)).
 #T1; #T2; #T3; #T4; #f1; #f2; #f3; #f4; #H1; #H2; #H3; #H4; #H5; #H6; #H7; #H8;
 #p1; nelim p1; #x1; #y1; #z1; #v1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #H;
 nchange with (((f1 x1 x2) ⊗ (f2 y1 y2) ⊗ (f3 z1 z2) ⊗ (f4 v1 v2)) = false);
 napply (or4_elim (x1 ≠ x2) (y1 ≠ y2) (z1 ≠ z2) (v1 ≠ v2) ? (quadruple_destruct T1 T2 T3 T4 H1 H2 H3 H4 … H) ?);
 ##[ ##1: #H9; nrewrite > (H5 … H9); nrewrite > (andb_false4_1 (f2 y1 y2) (f3 z1 z2) (f4 v1 v2)); napply refl_eq
 ##| ##2: #H9; nrewrite > (H6 … H9); nrewrite > (andb_false4_2 (f1 x1 x2) (f3 z1 z2) (f4 v1 v2)); napply refl_eq
 ##| ##3: #H9; nrewrite > (H7 … H9); nrewrite > (andb_false4_3 (f1 x1 x2) (f2 y1 y2) (f4 v1 v2)); napply refl_eq
 ##| ##4: #H9; nrewrite > (H8 … H9); nrewrite > (andb_false4_4 (f1 x1 x2) (f2 y1 y2) (f3 z1 z2)); napply refl_eq
 ##]
nqed.

(* ********* *)
(* TUPLE x 5 *)
(* ********* *)

nlemma quintuple_destruct_1 :
∀T1,T2,T3,T4,T5.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.∀w1,w2:T5.
 quintuple T1 T2 T3 T4 T5 x1 y1 z1 v1 w1 = quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 → x1 = x2.
 #T1; #T2; #T3; #T4; #T5; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #w1; #w2; #H;
 nchange with (match quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 with [ quintuple a _ _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quintuple_destruct_2 :
∀T1,T2,T3,T4,T5.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.∀w1,w2:T5.
 quintuple T1 T2 T3 T4 T5 x1 y1 z1 v1 w1 = quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 → y1 = y2.
 #T1; #T2; #T3; #T4; #T5; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #w1; #w2; #H;
 nchange with (match quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 with [ quintuple _ b _ _ _ ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quintuple_destruct_3 :
∀T1,T2,T3,T4,T5.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.∀w1,w2:T5.
 quintuple T1 T2 T3 T4 T5 x1 y1 z1 v1 w1 = quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 → z1 = z2.
 #T1; #T2; #T3; #T4; #T5; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #w1; #w2; #H;
 nchange with (match quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 with [ quintuple _ _ c _ _ ⇒ z1 = c ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quintuple_destruct_4 :
∀T1,T2,T3,T4,T5.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.∀w1,w2:T5.
 quintuple T1 T2 T3 T4 T5 x1 y1 z1 v1 w1 = quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 → v1 = v2.
 #T1; #T2; #T3; #T4; #T5; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #w1; #w2; #H;
 nchange with (match quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 with [ quintuple _ _ _ d _ ⇒ v1 = d ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma quintuple_destruct_5 :
∀T1,T2,T3,T4,T5.∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.∀w1,w2:T5.
 quintuple T1 T2 T3 T4 T5 x1 y1 z1 v1 w1 = quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 → w1 = w2.
 #T1; #T2; #T3; #T4; #T5; #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #w1; #w2; #H;
 nchange with (match quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2 with [ quintuple _ _ _ _ e ⇒ w1 = e ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqquintuple :
∀T1,T2,T3,T4,T5:Type.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.∀f5:T5 → T5 → bool.
 (symmetricT T1 bool f1) →
 (symmetricT T2 bool f2) →
 (symmetricT T3 bool f3) →
 (symmetricT T4 bool f4) →
 (symmetricT T5 bool f5) →
 (∀p1,p2:Prod5T T1 T2 T3 T4 T5.
  (eq_quintuple T1 T2 T3 T4 T5 f1 f2 f3 f4 f5 p1 p2 = eq_quintuple T1 T2 T3 T4 T5 f1 f2 f3 f4 f5 p2 p1)).
 #T1; #T2; #T3; #T4; #T5; #f1; #f2; #f3; #f4; #f5; #H; #H1; #H2; #H3; #H4;
 #p1; nelim p1; #x1; #y1; #z1; #v1; #w1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #w2;
 nnormalize;
 nrewrite > (H x1 x2);
 ncases (f1 x2 x1);
 nnormalize;
 ##[ ##1: nrewrite > (H1 y1 y2);
          ncases (f2 y2 y1);
          nnormalize;
          ##[ ##1: nrewrite > (H2 z1 z2);
                   ncases (f3 z2 z1);
                   nnormalize;
                   ##[ ##1: nrewrite > (H3 v1 v2);
                            ncases (f4 v2 v1);
                            nnormalize;
                            ##[ ##1: nrewrite > (H4 w1 w2); napply refl_eq
                            ##| ##2: napply refl_eq
                            ##]
                   ##| ##2: napply refl_eq
                   ##]
          ##| ##2: napply refl_eq
          ##]
 ##| ##2: napply refl_eq
 ##]
nqed.

nlemma eq_to_eqquintuple :
∀T1,T2,T3,T4,T5.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.∀f5:T5 → T5 → bool.
 (∀x,y:T1.x = y → f1 x y = true) →
 (∀x,y:T2.x = y → f2 x y = true) →
 (∀x,y:T3.x = y → f3 x y = true) →
 (∀x,y:T4.x = y → f4 x y = true) →
 (∀x,y:T5.x = y → f5 x y = true) →
 (∀p1,p2:Prod5T T1 T2 T3 T4 T5.
  (p1 = p2 → eq_quintuple T1 T2 T3 T4 T5 f1 f2 f3 f4 f5 p1 p2 = true)).
 #T1; #T2; #T3; #T4; #T5; #f1; #f2; #f3; #f4; #f5; #H1; #H2; #H3; #H4; #H5;
 #p1; nelim p1; #x1; #y1; #z1; #v1; #w1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #w2; #H;
 nnormalize;
 nrewrite > (H1 … (quintuple_destruct_1 … H));
 nnormalize;
 nrewrite > (H2 … (quintuple_destruct_2 … H));
 nnormalize;
 nrewrite > (H3 … (quintuple_destruct_3 … H));
 nnormalize;
 nrewrite > (H4 … (quintuple_destruct_4 … H));
 nnormalize;
 nrewrite > (H5 … (quintuple_destruct_5 … H));
 napply refl_eq.
nqed.

nlemma eqquintuple_to_eq :
∀T1,T2,T3,T4,T5.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.∀f5:T5 → T5 → bool.
 (∀x,y:T1.f1 x y = true → x = y) →
 (∀x,y:T2.f2 x y = true → x = y) →
 (∀x,y:T3.f3 x y = true → x = y) →
 (∀x,y:T4.f4 x y = true → x = y) →
 (∀x,y:T5.f5 x y = true → x = y) →
 (∀p1,p2:Prod5T T1 T2 T3 T4 T5.
  (eq_quintuple T1 T2 T3 T4 T5 f1 f2 f3 f4 f5 p1 p2 = true → p1 = p2)).
 #T1; #T2; #T3; #T4; #T5; #f1; #f2; #f3; #f4; #f5; #H1; #H2; #H3; #H4; #H5;
 #p1; nelim p1; #x1; #y1; #z1; #v1; #w1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #w2; #H;
 nnormalize in H:(%);
 nletin K ≝ (H1 x1 x2);
 ncases (f1 x1 x2) in H:(%) K:(%);
 nnormalize;
 ##[ ##2: #H6; ndestruct (*napply (bool_destruct … H6)*) ##]
 nletin K1 ≝ (H2 y1 y2);
 ncases (f2 y1 y2) in K1:(%) ⊢ %;
 nnormalize;
 ##[ ##2: #H6; #H7; ndestruct (*napply (bool_destruct … H7)*) ##]
 nletin K2 ≝ (H3 z1 z2);
 ncases (f3 z1 z2) in K2:(%) ⊢ %;
 nnormalize;
 ##[ ##2: #H6; #H7; #H8; ndestruct (*napply (bool_destruct … H8)*) ##]
 nletin K3 ≝ (H4 v1 v2);
 ncases (f4 v1 v2) in K3:(%) ⊢ %;
 nnormalize;
 ##[ ##2: #H6; #H7; #H8; #H9; ndestruct (*napply (bool_destruct … H9)*) ##]
 #H6; #H7; #H8; #H9; #H10;
 nrewrite > (H6 (refl_eq …));
 nrewrite > (H7 (refl_eq …));
 nrewrite > (H8 (refl_eq …));
 nrewrite > (H10 (refl_eq …));
 nrewrite > (H5 w1 w2 H9);
 napply refl_eq.
nqed.

nlemma decidable_quintuple :
∀T1,T2,T3,T4,T5.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T4.decidable (x = y)) →
 (∀x,y:T5.decidable (x = y)) →
 (∀x,y:Prod5T T1 T2 T3 T4 T5.decidable (x = y)).
 #T1; #T2; #T3; #T4; #T5; #H; #H1; #H2; #H3; #H4;
 #x; nelim x; #xx1; #xx2; #xx3; #xx4; #xx5;
 #y; nelim y; #yy1; #yy2; #yy3; #yy4; #yy5;
 nnormalize;
 napply (or2_elim (xx1 = yy1) (xx1 ≠ yy1) ? (H xx1 yy1) ?);
 ##[ ##2: #H5; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
          nnormalize; #H6; napply (H5 (quintuple_destruct_1 T1 T2 T3 T4 T5 … H6))
 ##| ##1: #H5; napply (or2_elim (xx2 = yy2) (xx2 ≠ yy2) ? (H1 xx2 yy2) ?);
          ##[ ##2: #H6; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H7; napply (H6 (quintuple_destruct_2 T1 T2 T3 T4 T5 … H7))
          ##| ##1: #H6; napply (or2_elim (xx3 = yy3) (xx3 ≠ yy3) ? (H2 xx3 yy3) ?);
                   ##[ ##2: #H7; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H8; napply (H7 (quintuple_destruct_3 T1 T2 T3 T4 T5 … H8))
                   ##| ##1: #H7; napply (or2_elim (xx4 = yy4) (xx4 ≠ yy4) ? (H3 xx4 yy4) ?);
                            ##[ ##2: #H8; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                     nnormalize; #H9; napply (H8 (quintuple_destruct_4 T1 T2 T3 T4 T5 … H9))
                            ##| ##1: #H8; napply (or2_elim (xx5 = yy5) (xx5 ≠ yy5) ? (H4 xx5 yy5) ?);
                                     ##[ ##2: #H9; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                              nnormalize; #H10; napply (H9 (quintuple_destruct_5 T1 T2 T3 T4 T5 … H10))
                                     ##| ##1: #H9; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                                              nrewrite > H5;
                                              nrewrite > H6;
                                              nrewrite > H7;
                                              nrewrite > H8;
                                              nrewrite > H9;
                                              napply refl_eq
                                     ##]
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma neqquintuple_to_neq :
∀T1,T2,T3,T4,T5.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.∀f5:T5 → T5 → bool.
 (∀x,y:T1.f1 x y = false → x ≠ y) →
 (∀x,y:T2.f2 x y = false → x ≠ y) →
 (∀x,y:T3.f3 x y = false → x ≠ y) →
 (∀x,y:T4.f4 x y = false → x ≠ y) →
 (∀x,y:T5.f5 x y = false → x ≠ y) →
 (∀p1,p2:Prod5T T1 T2 T3 T4 T5. 
  (eq_quintuple T1 T2 T3 T4 T5 f1 f2 f3 f4 f5 p1 p2 = false → p1 ≠ p2)).
 #T1; #T2; #T3; #T4; #T5; #f1; #f2; #f3; #f4; #f5; #H1; #H2; #H3; #H4; #H5;
 #p1; nelim p1; #x1; #y1; #z1; #v1; #w1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #w2;
 nchange with ((((f1 x1 x2) ⊗ (f2 y1 y2) ⊗ (f3 z1 z2) ⊗ (f4 v1 v2) ⊗ (f5 w1 w2)) = false) → ?); #H;
 nnormalize; #H6;
 napply (or5_elim ((f1 x1 x2) = false) ((f2 y1 y2) = false) ((f3 z1 z2) = false) ((f4 v1 v2) = false) ((f5 w1 w2) = false) ? (andb_false5 … H) ?);
 ##[ ##1: #H7; napply (H1 x1 x2 H7); napply (quintuple_destruct_1 T1 T2 T3 T4 T5 … H6)
 ##| ##2: #H7; napply (H2 y1 y2 H7); napply (quintuple_destruct_2 T1 T2 T3 T4 T5 … H6)
 ##| ##3: #H7; napply (H3 z1 z2 H7); napply (quintuple_destruct_3 T1 T2 T3 T4 T5 … H6)
 ##| ##4: #H7; napply (H4 v1 v2 H7); napply (quintuple_destruct_4 T1 T2 T3 T4 T5 … H6)
 ##| ##5: #H7; napply (H5 w1 w2 H7); napply (quintuple_destruct_5 T1 T2 T3 T4 T5 … H6)
 ##]
nqed.

nlemma quintuple_destruct :
∀T1,T2,T3,T4,T5.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T4.decidable (x = y)) →
 (∀x,y:T5.decidable (x = y)) →
 (∀x1,x2:T1.∀y1,y2:T2.∀z1,z2:T3.∀v1,v2:T4.∀w1,w2:T5.
  (quintuple T1 T2 T3 T4 T5 x1 y1 z1 v1 w1) ≠ (quintuple T1 T2 T3 T4 T5 x2 y2 z2 v2 w2) →
  Or5 (x1 ≠ x2) (y1 ≠ y2) (z1 ≠ z2) (v1 ≠ v2) (w1 ≠ w2)).
 #T1; #T2; #T3; #T4; #T5; #H1; #H2; #H3; #H4; #H5;
 #x1; #x2; #y1; #y2; #z1; #z2; #v1; #v2; #w1; #w2;
 nnormalize; #H;
 napply (or2_elim (x1 = x2) (x1 ≠ x2) ? (H1 x1 x2) ?);
 ##[ ##2: #H6; napply (or5_intro1 … H6)
 ##| ##1: #H6; napply (or2_elim (y1 = y2) (y1 ≠ y2) ? (H2 y1 y2) ?);
          ##[ ##2: #H7; napply (or5_intro2 … H7)
          ##| ##1: #H7; napply (or2_elim (z1 = z2) (z1 ≠ z2) ? (H3 z1 z2) ?);
                   ##[ ##2: #H8; napply (or5_intro3 … H8)
                   ##| ##1: #H8; napply (or2_elim (v1 = v2) (v1 ≠ v2) ? (H4 v1 v2) ?);
                            ##[ ##2: #H9; napply (or5_intro4 … H9)
                            ##| ##1: #H9; napply (or2_elim (w1 = w2) (w1 ≠ w2) ? (H5 w1 w2) ?);
                                     ##[ ##2: #H10; napply (or5_intro5 … H10)
                                     ##| ##1: #H10; nrewrite > H6 in H:(%);
                                              nrewrite > H7;
                                              nrewrite > H8;
                                              nrewrite > H9;
                                              nrewrite > H10; #H; nelim (H (refl_eq …))
                                     ##]
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_neqquintuple :
∀T1,T2,T3,T4,T5.
∀f1:T1 → T1 → bool.∀f2:T2 → T2 → bool.∀f3:T3 → T3 → bool.∀f4:T4 → T4 → bool.∀f5:T5 → T5 → bool.
 (∀x,y:T1.decidable (x = y)) →
 (∀x,y:T2.decidable (x = y)) →
 (∀x,y:T3.decidable (x = y)) →
 (∀x,y:T4.decidable (x = y)) →
 (∀x,y:T5.decidable (x = y)) →
 (∀x,y:T1.x ≠ y → f1 x y = false) →
 (∀x,y:T2.x ≠ y → f2 x y = false) →
 (∀x,y:T3.x ≠ y → f3 x y = false) →
 (∀x,y:T4.x ≠ y → f4 x y = false) →
 (∀x,y:T5.x ≠ y → f5 x y = false) →
 (∀p1,p2:Prod5T T1 T2 T3 T4 T5. 
  (p1 ≠ p2 → eq_quintuple T1 T2 T3 T4 T5 f1 f2 f3 f4 f5 p1 p2 = false)).
 #T1; #T2; #T3; #T4; #T5; #f1; #f2; #f3; #f4; #f5; 
 #H1; #H2; #H3; #H4; #H5; #H6; #H7; #H8; #H9; #H10;
 #p1; nelim p1; #x1; #y1; #z1; #v1; #w1;
 #p2; nelim p2; #x2; #y2; #z2; #v2; #w2; #H;
 nchange with (((f1 x1 x2) ⊗ (f2 y1 y2) ⊗ (f3 z1 z2) ⊗ (f4 v1 v2) ⊗ (f5 w1 w2)) = false);
 napply (or5_elim (x1 ≠ x2) (y1 ≠ y2) (z1 ≠ z2) (v1 ≠ v2) (w1 ≠ w2) ? (quintuple_destruct T1 T2 T3 T4 T5 H1 H2 H3 H4 H5 … H) ?);
 ##[ ##1: #H11; nrewrite > (H6 … H11); nrewrite > (andb_false5_1 (f2 y1 y2) (f3 z1 z2) (f4 v1 v2) (f5 w1 w2)); napply refl_eq
 ##| ##2: #H11; nrewrite > (H7 … H11); nrewrite > (andb_false5_2 (f1 x1 x2) (f3 z1 z2) (f4 v1 v2) (f5 w1 w2)); napply refl_eq
 ##| ##3: #H11; nrewrite > (H8 … H11); nrewrite > (andb_false5_3 (f1 x1 x2) (f2 y1 y2) (f4 v1 v2) (f5 w1 w2)); napply refl_eq
 ##| ##4: #H11; nrewrite > (H9 … H11); nrewrite > (andb_false5_4 (f1 x1 x2) (f2 y1 y2) (f3 z1 z2) (f5 w1 w2)); napply refl_eq
 ##| ##5: #H11; nrewrite > (H10 … H11); nrewrite > (andb_false5_5 (f1 x1 x2) (f2 y1 y2) (f3 z1 z2) (f4 v1 v2)); napply refl_eq
 ##]
nqed.
