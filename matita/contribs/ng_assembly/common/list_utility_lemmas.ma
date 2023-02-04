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

include "common/list_utility.ma".
include "common/list_lemmas.ma".

(* *************** *)
(* LISTE GENERICHE *)
(* *************** *)

nlemma symmetric_lenlist : ∀T.∀l1,l2:list T.len_list T l1 = len_list T l2 → len_list T l2 = len_list T l1.
 #T; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2; nnormalize;
          ##[ ##1: #H; napply refl_eq
          ##| ##2: #h; #t; #H; ndestruct (*nelim (nat_destruct_0_S ? H)*)
          ##]
 ##| ##2: #h; #l2; ncases l2; nnormalize;
          ##[ ##1: #H; #l; #H1; nrewrite < H1; napply refl_eq
          ##| ##2: #h; #l; #H; #l3; #H1; nrewrite < H1; napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightlist2_aux :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:list T1.
  ∀H1:(len_list T1 l1 = len_list T1 l2).
  ∀H2:(len_list T1 l2 = len_list T1 l1).
   (fold_right_list2 T1 T2 f acc l1 l2 H1 = fold_right_list2 T1 T2 f acc l2 l1 H2)).
 #T1; #T2; #f; #H; #acc; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H1; #H2; napply refl_eq
          ##| ##2: #h; #l; #H1; #H2;
                   nchange in H1:(%) with (O = (S (len_list ? l)));
                   ndestruct (*nelim (nat_destruct_0_S ? H1)*)
          ##]
 ##| ##2: #h3; #l3; #H1; #l2; ncases l2;
          ##[ ##1: #H2; #H3; nchange in H2:(%) with ((S (len_list ? l3)) = O);
                   ndestruct (*nelim (nat_destruct_S_0 ? H1)*)
          ##| ##2: #h4; #l4; #H2; #H3;
                   nchange in H2:(%) with ((S (len_list ? l3)) = (S (len_list ? l4)));
                   nchange in H3:(%) with ((S (len_list ? l4)) = (S (len_list ? l3)));
                   nchange with ((f h3 h4 (fold_right_list2 T1 T2 f acc l3 l4 (fold_right_list2_aux3 T1 h3 h4 l3 l4 ?))) =
                                 (f h4 h3 (fold_right_list2 T1 T2 f acc l4 l3 (fold_right_list2_aux3 T1 h4 h3 l4 l3 ?))));
                   nrewrite < (H1 l4 (fold_right_list2_aux3 T1 h3 h4 l3 l4 H2) (fold_right_list2_aux3 T1 h4 h3 l4 l3 H3));
                   nrewrite > (H h3 h4 (fold_right_list2 T1 T2 f acc l3 l4 ?));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightlist2 :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:list T1.∀H:len_list T1 l1 = len_list T1 l2.
   fold_right_list2 T1 T2 f acc l1 l2 H = fold_right_list2 T1 T2 f acc l2 l1 (symmetric_lenlist T1 l1 l2 H)).
 #T1; #T2; #f; #H; #acc; #l1; #l2; #H1;
 nrewrite > (symmetric_foldrightlist2_aux T1 T2 f H acc l1 l2 H1 (symmetric_lenlist T1 l1 l2 H1));
 napply refl_eq.
nqed.

nlemma symmetric_bfoldrightlist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.f x y = f y x) →
 (∀l1,l2:list T1.
  bfold_right_list2 T1 f l1 l2 = bfold_right_list2 T1 f l2 l1).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize;
                   nrewrite > (H1 ll2);
                   nrewrite > (H hh1 hh2);
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightlist2_to_eq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = true → x = y)) →
 (∀l1,l2:list T1.
  (bfold_right_list2 T1 f l1 l2 = true → l1 = l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: #H1; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: nnormalize; #H2;
                   ndestruct (*napply (bool_destruct … H2)*)
          ##| ##2: #hh2; #ll2; #H2;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_list2 T f ll1 ll2)) = true);
                   nrewrite > (H hh1 hh2 (andb_true_true_l … H2));
                   nrewrite > (H1 ll2 (andb_true_true_r … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma eq_to_bfoldrightlist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(x = y → f x y = true)) →
 (∀l1,l2:list T1.
  (l1 = l2 → bfold_right_list2 T1 f l1 l2 = true)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: #H1; nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; #H1;
                   (* !!! ndestruct: assert false *)
                   nelim (list_destruct_nil_cons ??? H1)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #H2;
                   (* !!! ndestruct: assert false *)
                   nelim (list_destruct_cons_nil ??? H2)
          ##| ##2: #hh2; #ll2; #H2; nnormalize;
                   nrewrite > (list_destruct_1 … H2);
                   nrewrite > (H hh2 hh2 (refl_eq …));
                   nnormalize;
                   nrewrite > (H1 ll2 (list_destruct_2 … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightlist2_to_lenlist :
∀T.∀f:T → T → bool.
 (∀l1,l2:list T.bfold_right_list2 T f l1 l2 = true → len_list T l1 = len_list T l2).
 #T; #f; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H; napply refl_eq
          ##| ##2: nnormalize; #hh; #tt; #H;
                   ndestruct (*napply (bool_destruct … H)*)
          ##]
 ##| ##2: #hh; #tt; #H; #l2; ncases l2;
          ##[ ##1: nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #hh1; #tt1; #H1; nnormalize;
                   nrewrite > (H tt1 ?);
                   ##[ ##1: napply refl_eq
                   ##| ##2: nchange in H1:(%) with ((? ⊗ (bfold_right_list2 T f tt tt1)) = true);
                            napply (andb_true_true_r … H1)
                   ##]
          ##]
 ##]
nqed.

nlemma decidable_list :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀x,y:list T.decidable (x = y)).
 #T; #H; #x; nelim x;
 ##[ ##1: #y; ncases y;
          ##[ ##1: nnormalize; napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H1;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_nil_cons T … H1)
          ##]
 ##| ##2: #hh1; #tt1; #H1; #y; ncases y;
          ##[ ##1: nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_cons_nil T … H2)
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H …));
                   ##[ ##2: #H2; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H3; napply (H2 (list_destruct_1 T … H3))
                   ##| ##1: #H2; napply (or2_elim (tt1 = tt2) (tt1 ≠ tt2) ? (H1 tt2));
                            ##[ ##2: #H3; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                     nnormalize; #H4; napply (H3 (list_destruct_2 T … H4))
                            ##| ##1: #H3; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                                     nrewrite > H2; nrewrite > H3; napply refl_eq
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma nbfoldrightlist2_to_neq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = false → x ≠ y)) →
 (∀l1,l2:list T1.
  (bfold_right_list2 T1 f l1 l2 = false → l1 ≠ l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #hh2; #ll2; #H1; nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #H2; nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2; nnormalize; #H3;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_list2 T f ll1 ll2)) = false);
                   napply (H1 ll2 ? (list_destruct_2 T … H3));
                   napply (or2_elim ??? (andb_false2 … H2) );
                   ##[ ##1: #H4; napply (absurd (hh1 = hh2) …);
                            ##[ ##1: nrewrite > (list_destruct_1 T … H3); napply refl_eq
                            ##| ##2: napply (H … H4)
                            ##]
                   ##| ##2: #H4; napply H4
                   ##]
          ##]
 ##]
nqed.

nlemma list_destruct :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀h1,h2:T.∀l1,l2:list T.
    (h1::l1) ≠ (h2::l2) → h1 ≠ h2 ∨ l1 ≠ l2).
 #T; #H; #h1; #h2; #l1; nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: #H1; napply (or2_intro1 (h1 ≠ h2) ([] ≠ []) …);
                   nnormalize; #H2; nrewrite > H2 in H1:(%);
                   nnormalize; #H1; napply (H1 (refl_eq …))
          ##| ##2: #hh2; #ll2; #H1; napply (or2_intro2 (h1 ≠ h2) ([] ≠ (hh2::ll2)) …);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #H2; napply (or2_intro2 (h1 ≠ h2) ((hh1::ll1) ≠ []) …);
                   nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (list_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2;     
                   napply (or2_elim (h1 = h2) (h1 ≠ h2) ? (H h1 h2) …);
                   ##[ ##2: #H3; napply (or2_intro1 (h1 ≠ h2) ((hh1::ll1) ≠ (hh2::ll2)) H3)
                   ##| ##1: #H3; napply (or2_intro2 (h1 ≠ h2) ((hh1::ll1) ≠ (hh2::ll2) …));
                            nrewrite > H3 in H2:(%); #H2;
                            nnormalize; #H4; nrewrite > (list_destruct_1 T … H4) in H2:(%); #H2;
                            nrewrite > (list_destruct_2 T … H4) in H2:(%); #H2;
                            napply (H2 (refl_eq …))
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_nbfoldrightlist2 :
∀T:Type.∀f:T → T → bool.
 (∀x,y:T.decidable (x = y)) →
 (∀x,y.(x ≠ y → f x y = false)) →
 (∀l1,l2:list T.
  (l1 ≠ l2 → bfold_right_list2 T f l1 l2 = false)).
 #T; #f; #H; #H1; #l1;
 nelim l1;
 ##[ ##1: #l2; ncases l2;
          ##[ ##1: nnormalize; #H2; nelim (H2 (refl_eq …))
          ##| ##2: #hh2; #ll2; nnormalize; #H2; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H2; #l2; ncases l2;
          ##[ ##1: nnormalize; #H3; napply refl_eq
          ##| ##2: #hh2; #ll2; #H3;
                   nchange with (((f hh1 hh2)⊗(bfold_right_list2 T f ll1 ll2)) = false);
                   napply (or2_elim (hh1 ≠ hh2) (ll1 ≠ ll2) ? (list_destruct T H … H3) …);
                   ##[ ##1: #H4; nrewrite > (H1 hh1 hh2 H4); nnormalize; napply refl_eq
                   ##| ##2: #H4; nrewrite > (H2 ll2 H4);
                            nrewrite > (symmetric_andbool (f hh1 hh2) false);
                            nnormalize; napply refl_eq
                   ##]
          ##]
 ##]
nqed.

nlemma isbemptylist_to_isemptylist : ∀T,l.isb_empty_list T l = true → is_empty_list T l.
 #T; #l;
 ncases l;
 nnormalize;
 ##[ ##1: #H; napply I
 ##| ##2: #x; #l; #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma isnotbemptylist_to_isnotemptylist : ∀T,l.isnotb_empty_list T l = true → isnot_empty_list T l.
 #T; #l;
 ncases l;
 nnormalize;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##2: #x; #l; #H; napply I
 ##]
nqed.

(* ************** *)
(* NON-EMPTY LIST *)
(* ************** *)

nlemma symmetric_lennelist : ∀T.∀l1,l2:ne_list T.len_neList T l1 = len_neList T l2 → len_neList T l2 = len_neList T l1.
 #T; #l1;
 nelim l1;
 ##[ ##1: #h; #l2; ncases l2; nnormalize;
          ##[ ##1: #H; #H1; napply refl_eq
          ##| ##2: #h; #t; #H; nrewrite > H; napply refl_eq
          ##]
 ##| ##2: #h; #l2; ncases l2; nnormalize;
          ##[ ##1: #h1; #H; #l; #H1; nrewrite < H1; napply refl_eq
          ##| ##2: #h; #l; #H; #l3; #H1; nrewrite < H1; napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightnelist2_aux :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:ne_list T1.
  ∀H1:len_neList T1 l1 = len_neList T1 l2.∀H2:len_neList T1 l2 = len_neList T1 l1.
   fold_right_neList2 T1 T2 f acc l1 l2 H1 = fold_right_neList2 T1 T2 f acc l2 l1 H2).
 #T1; #T2; #f; #H; #acc; #l1;
 nelim l1;
 ##[ ##1: #h; #l2; ncases l2;
          ##[ ##1: #h1; nnormalize; #H1; #H2; nrewrite > (H h h1 acc); napply refl_eq
          ##| ##2: #h1; #l; ncases l;
                   ##[ ##1: #h3; #H1; #H2;
                            nchange in H1:(%) with ((S O) = (S (S O)));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_0_S ? (nat_destruct_S_S … H1))
                   ##| ##2: #h3; #l3; #H1; #H2;
                            nchange in H1:(%) with ((S O) = (S (S (len_neList ? l3))));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_0_S ? (nat_destruct_S_S … H1))
                   ##]                   
          ##]
 ##| ##2: #h3; #l3; #H1; #l2; ncases l2;
          ##[ ##1: #h4; ncases l3;
                   ##[ ##1: #h5; #H2; #H3;
                            nchange in H2:(%) with ((S (S O)) = (S O));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H2))
                   ##| ##2: #h5; #l5; #H2; #H3;
                            nchange in H2:(%) with ((S (S (len_neList ? l5))) = (S O));
                            (* !!! ndestruct: si inceppa su un'ipotesi che non e' H1 *)
                            nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H2))
                   ##]
          ##| ##2: #h4; #l4; #H2; #H3;
                   nchange in H2:(%) with ((S (len_neList ? l3)) = (S (len_neList ? l4)));
                   nchange in H3:(%) with ((S (len_neList ? l4)) = (S (len_neList ? l3)));
                   nchange with ((f h3 h4 (fold_right_neList2 T1 T2 f acc l3 l4 (fold_right_neList2_aux3 T1 h3 h4 l3 l4 ?))) =
                                 (f h4 h3 (fold_right_neList2 T1 T2 f acc l4 l3 (fold_right_neList2_aux3 T1 h4 h3 l4 l3 ?))));
                   nrewrite < (H1 l4 (fold_right_neList2_aux3 T1 h3 h4 l3 l4 H2) (fold_right_neList2_aux3 T1 h4 h3 l4 l3 H3));
                   nrewrite > (H h3 h4 (fold_right_neList2 T1 T2 f acc l3 l4 ?));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma symmetric_foldrightnelist2 :
∀T1,T2:Type.∀f:T1 → T1 → T2 → T2.
 (∀x,y,z.f x y z = f y x z) →
 (∀acc:T2.∀l1,l2:ne_list T1.∀H:len_neList T1 l1 = len_neList T1 l2.
  fold_right_neList2 T1 T2 f acc l1 l2 H = fold_right_neList2 T1 T2 f acc l2 l1 (symmetric_lennelist T1 l1 l2 H)).
 #T1; #T2; #f; #H; #acc; #l1; #l2; #H1;
 nrewrite > (symmetric_foldrightnelist2_aux T1 T2 f H acc l1 l2 H1 (symmetric_lennelist T1 l1 l2 H1));
 napply refl_eq.
nqed.

nlemma symmetric_bfoldrightnelist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.f x y = f y x) →
 (∀l1,l2:ne_list T1.
  bfold_right_neList2 T1 f l1 l2 = bfold_right_neList2 T1 f l2 l1).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; nrewrite > (H hh1 hh2); napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize;
                   nrewrite > (H1 ll2);
                   nrewrite > (H hh1 hh2);
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightnelist2_to_eq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = true → x = y)) →
 (∀l1,l2:ne_list T1.
  (bfold_right_neList2 T1 f l1 l2 = true → l1 = l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; #H1; nnormalize in H1:(%); nrewrite > (H hh1 hh2 H1); napply refl_eq
          ##| ##2: #hh2; #ll2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H2; ndestruct (*napply (bool_destruct … H2)*)
          ##| ##2: #hh2; #ll2; #H2;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_neList2 T f ll1 ll2)) = true);
                   nrewrite > (H hh1 hh2 (andb_true_true_l … H2));
                   nrewrite > (H1 ll2 (andb_true_true_r … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma eq_to_bfoldrightnelist2 :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(x = y → f x y = true)) →
 (∀l1,l2:ne_list T1.
  (l1 = l2 → bfold_right_neList2 T1 f l1 l2 = true)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; #H1; nnormalize;
                   nrewrite > (H hh1 hh2 (nelist_destruct_nil_nil … H1));
                   napply refl_eq
          ##| ##2: #hh2; #ll2; #H1;
                   (* !!! ndestruct: assert false *)
                   nelim (nelist_destruct_nil_cons ???? H1)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; #H2;
                   (* !!! ndestruct: assert false *)
                   nelim (nelist_destruct_cons_nil ???? H2)
          ##| ##2: #hh2; #ll2; #H2; nnormalize;
                   nrewrite > (nelist_destruct_cons_cons_1 … H2);
                   nrewrite > (H hh2 hh2 (refl_eq …));
                   nnormalize;
                   nrewrite > (H1 ll2 (nelist_destruct_cons_cons_2 … H2));
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma bfoldrightnelist2_to_lennelist :
∀T.∀f:T → T → bool.
 (∀l1,l2:ne_list T.bfold_right_neList2 T f l1 l2 = true → len_neList T l1 = len_neList T l2).
 #T; #f; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: nnormalize; #hh2; #H; napply refl_eq
          ##| ##2: nnormalize; #hh2; #tt2; #H; ndestruct (*napply (bool_destruct … H)*)
          ##]
 ##| ##2: #hh1; #tt1; #H; #l2; ncases l2;
          ##[ ##1: nnormalize; #hh2; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #hh2; #tt2; #H1; nnormalize;
                   nrewrite > (H tt2 ?);
                   ##[ ##1: napply refl_eq
                   ##| ##2: nchange in H1:(%) with ((? ⊗ (bfold_right_neList2 T f tt1 tt2)) = true);
                            napply (andb_true_true_r … H1)
                   ##]
          ##]
 ##]
nqed.

nlemma decidable_nelist :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀x,y:ne_list T.decidable (x = y)).
 #T; #H; #x; nelim x;
 ##[ ##1: #hh1; #y; ncases y;
          ##[ ##1: #hh2; nnormalize; napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H hh1 hh2));
                   ##[ ##1: #H1; nrewrite > H1; napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
                   ##| ##2: #H1; napply (or2_intro2 (? = ?) (? ≠ ?) ?); nnormalize;
                            #H2; napply (H1 (nelist_destruct_nil_nil T … H2))
                   ##]
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H1;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_nil_cons T … H1)
          ##]
 ##| ##2: #hh1; #tt1; #H1; #y; ncases y;
          ##[ ##1: #hh1; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_cons_nil T … H2)
          ##| ##2: #hh2; #tt2; nnormalize; napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H …));
                   ##[ ##2: #H2; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H3; napply (H2 (nelist_destruct_cons_cons_1 T … H3))
                   ##| ##1: #H2; napply (or2_elim (tt1 = tt2) (tt1 ≠ tt2) ? (H1 tt2));
                            ##[ ##2: #H3; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                                     nnormalize; #H4; napply (H3 (nelist_destruct_cons_cons_2 T … H4))
                            ##| ##1: #H3; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                                     nrewrite > H2; nrewrite > H3; napply refl_eq
                            ##]
                   ##]
          ##]
 ##]
nqed.

nlemma nbfoldrightnelist2_to_neq :
∀T1:Type.∀f:T1 → T1 → bool.
 (∀x,y.(f x y = false → x ≠ y)) →
 (∀l1,l2:ne_list T1.
  (bfold_right_neList2 T1 f l1 l2 = false → l1 ≠ l2)).
 #T; #f; #H; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H1; #H2; napply (H hh1 hh2 H1 (nelist_destruct_nil_nil T … H2))
          ##| ##2: #hh2; #ll2; #H1; nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; #H2; nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2; nnormalize; #H3;
                   nchange in H2:(%) with (((f hh1 hh2)⊗(bfold_right_neList2 T f ll1 ll2)) = false);
                   napply (H1 ll2 ? (nelist_destruct_cons_cons_2 T … H3));
                   napply (or2_elim ??? (andb_false2 … H2) );
                   ##[ ##1: #H4; napply (absurd (hh1 = hh2) …);
                            ##[ ##1: nrewrite > (nelist_destruct_cons_cons_1 T … H3); napply refl_eq
                            ##| ##2: napply (H … H4)
                            ##]
                   ##| ##2: #H4; napply H4
                   ##]
          ##]
 ##]
nqed.

nlemma nelist_destruct :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀h1,h2:T.∀l1,l2:ne_list T.
    (h1§§l1) ≠ (h2§§l2) → h1 ≠ h2 ∨ l1 ≠ l2).
 #T; #H; #h1; #h2; #l1; nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; #H1; napply (or2_elim (h1 = h2) (h1 ≠ h2) ? (H …) …);
                   ##[ ##2: #H2; napply (or2_intro1 (h1 ≠ h2) («£hh1» ≠ «£hh2») H2)
                   ##| ##1: #H2; nrewrite > H2 in H1:(%); #H1;
                            napply (or2_elim (hh1 = hh2) (hh1 ≠ hh2) ? (H …) …);
                            ##[ ##2: #H3; napply (or2_intro2 (h2 ≠ h2) («£hh1» ≠ «£hh2») ?);
                                     nnormalize; #H4; napply (H3 (nelist_destruct_nil_nil T … H4))
                            ##| ##1: #H3; nrewrite > H3 in H1:(%); #H1; nelim (H1 (refl_eq …))
                            ##]
                   ##]
          ##| ##2: #hh2; #ll2; #H1; napply (or2_intro2 (h1 ≠ h2) («£hh1» ≠ (hh2§§ll2)) …);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_nil_cons T … H2)
          ##]
 ##| ##2: #hh1; #ll1; #H1; #l2; ncases l2;
          ##[ ##1: #hh2; #H2; napply (or2_intro2 (h1 ≠ h2) ((hh1§§ll1) ≠ «£hh2») …);
                   nnormalize; #H3;
                   (* !!! ndestruct: assert false *)
                   napply (nelist_destruct_cons_nil T … H3)
          ##| ##2: #hh2; #ll2; #H2;     
                   napply (or2_elim (h1 = h2) (h1 ≠ h2) ? (H h1 h2) …);
                   ##[ ##2: #H3; napply (or2_intro1 (h1 ≠ h2) ((hh1§§ll1) ≠ (hh2§§ll2)) H3)
                   ##| ##1: #H3; napply (or2_intro2 (h1 ≠ h2) ((hh1§§ll1) ≠ (hh2§§ll2) …));
                            nrewrite > H3 in H2:(%); #H2;
                            nnormalize; #H4; nrewrite > (nelist_destruct_cons_cons_1 T … H4) in H2:(%); #H2;
                            nrewrite > (nelist_destruct_cons_cons_2 T … H4) in H2:(%); #H2;
                            napply (H2 (refl_eq …))
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_nbfoldrightnelist2 :
∀T:Type.∀f:T → T → bool.
 (∀x,y:T.decidable (x = y)) →
 (∀x,y.(x ≠ y → f x y = false)) →
 (∀l1,l2:ne_list T.
  (l1 ≠ l2 → bfold_right_neList2 T f l1 l2 = false)).
 #T; #f; #H; #H1; #l1;
 nelim l1;
 ##[ ##1: #hh1; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H2; napply (H1 hh1 hh2 ?);
                   nnormalize; #H3; nrewrite > H3 in H2:(%); #H2; napply (H2 (refl_eq …))
          ##| ##2: #hh2; #ll2; nnormalize; #H2; napply refl_eq
          ##]
 ##| ##2: #hh1; #ll1; #H2; #l2; ncases l2;
          ##[ ##1: #hh2; nnormalize; #H3; napply refl_eq
          ##| ##2: #hh2; #ll2; #H3;
                   nchange with (((f hh1 hh2)⊗(bfold_right_neList2 T f ll1 ll2)) = false);
                   napply (or2_elim (hh1 ≠ hh2) (ll1 ≠ ll2) ? (nelist_destruct T H … H3) …);
                   ##[ ##1: #H4; nrewrite > (H1 hh1 hh2 H4); nnormalize; napply refl_eq
                   ##| ##2: #H4; nrewrite > (H2 ll2 H4);
                            nrewrite > (symmetric_andbool (f hh1 hh2) false);
                            nnormalize; napply refl_eq
                   ##]
          ##]
 ##]
nqed.
