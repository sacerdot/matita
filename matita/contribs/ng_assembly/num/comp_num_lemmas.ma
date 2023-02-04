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

include "num/comp_num.ma".
include "num/bool_lemmas.ma".

(* **** *)
(* BYTE *)
(* **** *)

nlemma cn_destruct_1 :
∀T.∀x1,x2,y1,y2:T.
 mk_comp_num T x1 y1 = mk_comp_num T x2 y2 → x1 = x2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match mk_comp_num ? x2 y2 with [ mk_comp_num a _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma cn_destruct_2 :
∀T.∀x1,x2,y1,y2:T.
 mk_comp_num T x1 y1 = mk_comp_num T x2 y2 → y1 = y2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match mk_comp_num ? x2 y2 with [ mk_comp_num _ b ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqcn :
∀T.∀feq:T → T → bool.
 (symmetricT T bool feq) →
 (symmetricT (comp_num T) bool (eq2_cn T feq)).
 #T; #feq; #H;
 #b1; nelim b1; #e1; #e2;
 #b2; nelim b2; #e3; #e4;
 nchange with (((feq e1 e3)⊗(feq e2 e4)) = ((feq e3 e1)⊗(feq e4 e2)));
 nrewrite > (H e1 e3);
 nrewrite > (H e2 e4);
 napply refl_eq.
nqed.

nlemma eqcn_to_eq :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(feq x y = true) → (x = y)) →
 (∀b1,b2:comp_num T.
  ((eq2_cn T feq b1 b2 = true) → (b1 = b2))).
 #T; #feq; #H; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 nchange in ⊢ (% → ?) with (((feq e1 e3)⊗(feq e2 e4)) = true);
 #H1;
 nrewrite < (H … (andb_true_true_l … H1));
 nrewrite < (H … (andb_true_true_r … H1));
 napply refl_eq.
nqed.

nlemma eq_to_eqcn :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(x = y) → (feq x y = true)) →
 (∀b1,b2:comp_num T.
  ((b1 = b2) → (eq2_cn T feq b1 b2 = true))).
 #T; #feq; #H; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 #H1;
 nrewrite < (cn_destruct_1 … H1);
 nrewrite < (cn_destruct_2 … H1);
 nchange with (((feq e1 e1)⊗(feq e2 e2)) = true);
 nrewrite > (H e1 e1 (refl_eq …));
 nrewrite > (H e2 e2 (refl_eq …)); 
 nnormalize;
 napply refl_eq.
nqed.

nlemma decidable_cn_aux1 :
∀T.∀e1,e2,e3,e4:T.e1 ≠ e3 → (mk_comp_num T e1 e2) ≠ (mk_comp_num T e3 e4).
 #T; #e1; #e2; #e3; #e4;
 nnormalize; #H; #H1;
 napply (H (cn_destruct_1 … H1)).
nqed.

nlemma decidable_cn_aux2 :
∀T.∀e1,e2,e3,e4:T.e2 ≠ e4 → (mk_comp_num T e1 e2) ≠ (mk_comp_num T e3 e4).
 #T; #e1; #e2; #e3; #e4;
 nnormalize; #H; #H1;
 napply (H (cn_destruct_2 … H1)).
nqed.

nlemma decidable_cn :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀b1,b2:comp_num T.
    (decidable (b1 = b2))).
 #T; #H;
 #b1; nelim b1; #e1; #e2;
 #b2; nelim b2; #e3; #e4;
 nnormalize;
 napply (or2_elim (e1 = e3) (e1 ≠ e3) ? (H e1 e3) …);
 ##[ ##2: #H1; napply (or2_intro2 … (decidable_cn_aux1 T e1 e2 e3 e4 H1))
 ##| ##1: #H1; napply (or2_elim (e2 = e4) (e2 ≠ e4) ? (H e2 e4) …);
          ##[ ##2: #H2; napply (or2_intro2 … (decidable_cn_aux2 T e1 e2 e3 e4 H2))
          ##| ##1: #H2; nrewrite > H1; nrewrite > H2;
                        napply (or2_intro1 … (refl_eq ? (mk_comp_num T e3 e4)))
          ##]
 ##]
nqed.

nlemma neqcn_to_neq :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(feq x y = false) → (x ≠ y)) →
 (∀b1,b2:comp_num T.
  ((eq2_cn T feq b1 b2 = false) → (b1 ≠ b2))).
 #T; #feq; #H; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 nchange with ((((feq e1 e3) ⊗ (feq e2 e4)) = false) → ?);
 #H1;
 napply (or2_elim ((feq e1 e3) = false) ((feq e2 e4) = false) ? (andb_false2 … H1) …);
 ##[ ##1: #H2; napply (decidable_cn_aux1 … (H … H2))
 ##| ##2: #H2; napply (decidable_cn_aux2 … (H … H2))
 ##]
nqed.

nlemma cn_destruct :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀e1,e2,e3,e4:T.
    ((mk_comp_num T e1 e2) ≠ (mk_comp_num T e3 e4)) →
    ((e1 ≠ e3) ∨ (e2 ≠ e4))).
 #T; #H; #e1; #e2; #e3; #e4;
 nnormalize; #H1;
 napply (or2_elim (e1 = e3) (e1 ≠ e3) ? (H e1 e3) …);
 ##[ ##2: #H2; napply (or2_intro1 … H2)
 ##| ##1: #H2; napply (or2_elim (e2 = e4) (e2 ≠ e4) ? (H e2 e4) …);
          ##[ ##2: #H3; napply (or2_intro2 … H3)
          ##| ##1: #H3; nrewrite > H2 in H1:(%);
                   nrewrite > H3;
                   #H1; nelim (H1 (refl_eq …))
          ##]
 ##]
nqed.

nlemma neq_to_neqcn :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(x ≠ y) → (feq x y = false)) →
 (∀x,y:T.decidable (x = y)) →
 (∀b1,b2:comp_num T.
  ((b1 ≠ b2) → (eq2_cn T feq b1 b2 = false))).
 #T; #feq; #H; #H1; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 #H2; nchange with (((feq e1 e3) ⊗ (feq e2 e4)) = false);
 napply (or2_elim (e1 ≠ e3) (e2 ≠ e4) ? (cn_destruct T H1 e1 e2 e3 e4 … H2) …);
 ##[ ##1: #H3; nrewrite > (H … H3); nnormalize; napply refl_eq
 ##| ##2: #H3; nrewrite > (H … H3);
          nrewrite > (symmetric_andbool (feq e1 e3) false);
          nnormalize; napply refl_eq
 ##]
nqed.
