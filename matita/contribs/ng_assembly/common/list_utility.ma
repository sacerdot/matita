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

include "common/list.ma".
include "common/option.ma".
include "common/nat_lemmas.ma".

(* *************** *)
(* LISTE GENERICHE *)
(* *************** *)

(* listlen *)
nlet rec len_list (T:Type) (l:list T) on l ≝
 match l with [ nil ⇒ O | cons _ t ⇒ S (len_list T t) ].

(* vuota? *)
ndefinition is_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ True | cons _ _ ⇒ False ].

ndefinition isb_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ true | cons _ _ ⇒ false ].

ndefinition isnot_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ False | cons _ _ ⇒ True ].

ndefinition isnotb_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ false | cons _ _ ⇒ true ].

(* reverse *)
nlet rec reverse_list (T:Type) (l:list T) on l ≝
 match l with
  [ nil ⇒ nil T
  | cons h t ⇒ (reverse_list T t)@[h]
  ].

(* getFirst *)
ndefinition get_first_list ≝
λT:Type.λl:list T.match l with
 [ nil ⇒ None ?
 | cons h _ ⇒ Some ? h ].

(* getLast *)
ndefinition get_last_list ≝
λT:Type.λl:list T.match reverse_list T l with
 [ nil ⇒ None ?
 | cons h _ ⇒ Some ? h ].

(* cutFirst *)
ndefinition cut_first_list ≝
λT:Type.λl:list T.match l with
 [ nil ⇒ nil T
 | cons _ t ⇒ t ].

(* cutLast *)
ndefinition cut_last_list ≝
λT:Type.λl:list T.match reverse_list T l with
 [ nil ⇒ nil T
 | cons _ t ⇒ reverse_list T t ].

(* apply f *)
nlet rec apply_f_list (T1,T2:Type) (l:list T1) (f:T1 → T2) on l ≝
match l with
 [ nil ⇒ nil T2
 | cons h t ⇒ cons T2 (f h) (apply_f_list T1 T2 t f) ].

(* fold right *)
nlet rec fold_right_list (T1,T2:Type) (f:T1 → T2 → T2) (acc:T2) (l:list T1) on l ≝
  match l with
   [ nil ⇒ acc
   | cons h t ⇒ f h (fold_right_list T1 T2 f acc t)
   ].

(* double fold right *)
nlemma fold_right_list2_aux1 :
∀T.∀h,t.len_list T [] = len_list T (h::t) → False.
 #T; #h; #t;
 nnormalize;
 #H;
 ndestruct (*napply (nat_destruct_0_S ? H)*).
nqed.

nlemma fold_right_list2_aux2 :
∀T.∀h,t.len_list T (h::t) = len_list T [] → False.
 #T; #h; #t;
 nnormalize;
 #H;
 ndestruct (*napply (nat_destruct_S_0 ? H)*).
nqed.

nlemma fold_right_list2_aux3 :
∀T.∀h,h',t,t'.len_list T (h::t) = len_list T (h'::t') → len_list T t = len_list T t'.
 #T; #h; #h'; #t; #t';
 nelim t;
 nelim t';
 ##[ ##1: nnormalize; #H; napply refl_eq
 ##| ##2: #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S O) = (S (S (len_list T l'))));
          ndestruct (*nelim (nat_destruct_0_S ? (nat_destruct_S_S … H1))*)
 ##| ##3: #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S (S (len_list T l'))) = (S O));
          ndestruct (*nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H1))*)
 ##| ##4: #a; #l; #H; #a1; #l1; #H1; #H2;
          nchange in H2:(%) with ((S (S (len_list T l1))) = (S (S (len_list T l))));
          nchange with ((S (len_list T l1)) = (S (len_list T l)));
          nrewrite > (nat_destruct_S_S … H2);
          napply refl_eq
 ##]
nqed.

nlet rec fold_right_list2 (T1,T2:Type) (f:T1 → T1 → T2 → T2) (acc:T2) (l1:list T1) on l1 ≝
 match l1
  return λl1.Πl2.len_list T1 l1 = len_list T1 l2 → T2
 with
  [ nil ⇒ λl2.match l2 return λl2.len_list T1 [] = len_list T1 l2 → T2 with
   [ nil ⇒ λp:len_list T1 [] = len_list T1 [].acc
   | cons h t ⇒ λp:len_list T1 [] = len_list T1 (h::t).
    False_rect_Type0 ? (fold_right_list2_aux1 T1 h t p)
   ]
  | cons h t ⇒ λl2.match l2 return λl2.len_list T1 (h::t) = len_list T1 l2 → T2 with
   [ nil ⇒ λp:len_list T1 (h::t) = len_list T1 [].
    False_rect_Type0 ? (fold_right_list2_aux2 T1 h t p)
   | cons h' t' ⇒ λp:len_list T1 (h::t) = len_list T1 (h'::t').
    f h h' (fold_right_list2 T1 T2 f acc t t' (fold_right_list2_aux3 T1 h h' t t' p))
   ]
  ].

nlet rec bfold_right_list2 (T1:Type) (f:T1 → T1 → bool) (l1,l2:list T1) on l1 ≝
 match l1 with
  [ nil ⇒ match l2 with
   [ nil ⇒ true | cons h t ⇒ false ]
  | cons h t ⇒ match l2 with
   [ nil ⇒ false | cons h' t' ⇒ (f h h') ⊗ (bfold_right_list2 T1 f t t')
   ]
  ].

(* nth elem *)
nlet rec nth_list (T:Type) (l:list T) (n:nat) on l ≝
 match l with
  [ nil ⇒ None ?
  | cons h t ⇒ match n with
   [ O ⇒ Some ? h | S n' ⇒ nth_list T t n' ]
  ].

(* abs elem *)
ndefinition abs_list_aux1 : ∀T:Type.∀n.((len_list T []) > n) = true → False.
 #T; nnormalize; #n; #H; ndestruct (*napply (bool_destruct … H)*). nqed.

ndefinition abs_list_aux2 : ∀T:Type.∀h:T.∀t:list T.∀n.((len_list T (h::t)) > (S n) = true) → ((len_list T t) > n) = true.
 #T; #h; #t; #n; nnormalize; #H; napply H. nqed.

nlet rec abs_list (T:Type) (l:list T) on l ≝
 match l
  return λl.Πn.(((len_list T l) > n) = true) → T
 with
  [ nil ⇒ λn.λp:(((len_list T []) > n) = true).False_rect_Type0 ? (abs_list_aux1 T n p)
  | cons h t ⇒ λn.
   match n with
    [ O ⇒ λp:(((len_list T (h::t)) > O) = true).h
    | S n' ⇒ λp:(((len_list T (h::t)) > (S n')) = true).
     abs_list T t n' (abs_list_aux2 T h t n' p)
    ]
  ].

(* esempio: abs_list ? [ 1; 2; 3; 4 ] 2 (refl_eq …) = 0. *)

(* ************** *)
(* NON-EMPTY LIST *)
(* ************** *)

(* listlen *)
nlet rec len_neList (T:Type) (nl:ne_list T) on nl ≝
 match nl with [ ne_nil _ ⇒ (S O) | ne_cons _ t ⇒ S (len_neList T t) ].

(* reverse *)
nlet rec reverse_neList (T:Type) (nl:ne_list T) on nl ≝
 match nl with
  [ ne_nil h ⇒ ne_nil T h
  | ne_cons h t ⇒ (reverse_neList T t)&(ne_nil T h)
  ].

(* getFirst *)
ndefinition get_first_neList ≝
λT:Type.λnl:ne_list T.match nl with
 [ ne_nil h ⇒ h
 | ne_cons h _ ⇒ h ].

(* getLast *)
ndefinition get_last_neList ≝
λT:Type.λnl:ne_list T.match reverse_neList T nl with
 [ ne_nil h ⇒ h
 | ne_cons h _ ⇒ h ].

(* cutFirst *)
ndefinition cut_first_neList ≝
λT:Type.λnl:ne_list T.match nl with
 [ ne_nil h ⇒ ne_nil T h
 | ne_cons _ t ⇒ t ].

(* cutLast *)
ndefinition cut_last_neList ≝
λT:Type.λnl:ne_list T.match reverse_neList T nl with
 [ ne_nil h ⇒ ne_nil T h
 | ne_cons _ t ⇒ reverse_neList T t ].

(* apply f *)
nlet rec apply_f_neList (T1,T2:Type) (nl:ne_list T1) (f:T1 → T2) on nl ≝
match nl with
 [ ne_nil h ⇒ ne_nil T2 (f h)
 | ne_cons h t ⇒ ne_cons T2 (f h) (apply_f_neList T1 T2 t f) ].

(* fold right *)
nlet rec fold_right_neList (T1,T2:Type) (f:T1 → T2 → T2) (acc:T2) (nl:ne_list T1) on nl ≝
  match nl with
   [ ne_nil h ⇒ f h acc
   | ne_cons h t ⇒ f h (fold_right_neList T1 T2 f acc t)
   ].

(* double fold right *)
nlemma fold_right_neList2_aux1 :
∀T.∀h,h',t'.len_neList T «£h» = len_neList T (h'§§t') → False.
 #T; #h; #h'; #t';
 nnormalize;
 ncases t';
 nnormalize;
 ##[ ##1: #x; #H; ndestruct (*nelim (nat_destruct_0_S ? (nat_destruct_S_S … H))*)
 ##| ##2: #x; #l; #H; ndestruct (*nelim (nat_destruct_0_S ? (nat_destruct_S_S … H))*)
 ##]
nqed.

nlemma fold_right_neList2_aux2 :
∀T.∀h,h',t.len_neList T (h§§t) = len_neList T «£h'» → False.
 #T; #h; #h'; #t;
 nnormalize;
 ncases t;
 nnormalize;
 ##[ ##1: #x; #H; ndestruct (*nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H))*)
 ##| ##2: #x; #l; #H; ndestruct (*nelim (nat_destruct_S_0 ? (nat_destruct_S_S … H))*)
 ##]
nqed.

nlemma fold_right_neList2_aux3 :
∀T.∀h,h',t,t'.len_neList T (h§§t) = len_neList T (h'§§t') → len_neList T t = len_neList T t'.
 #T; #h; #h'; #t; #t';
 nelim t;
 nelim t';
 ##[ ##1: nnormalize; #x; #y; #H; napply refl_eq
 ##| ##2: #a; #l'; #H; #x; #H1;
          nchange in H1:(%) with ((S (len_neList T «£x»)) = (S (len_neList T (a§§l'))));
          nrewrite > (nat_destruct_S_S … H1);
          napply refl_eq
 ##| ##3: #x; #a; #l'; #H; #H1;
          nchange in H1:(%) with ((S (len_neList T (a§§l')))= (S (len_neList T «£x»)));
          nrewrite > (nat_destruct_S_S … H1);
          napply refl_eq
 ##| ##4: #a; #l; #H; #a1; #l1; #H1; #H2;
          nchange in H2:(%) with ((S (len_neList T (a1§§l1))) = (S (len_neList T (a§§l))));
          nrewrite > (nat_destruct_S_S … H2);
          napply refl_eq
 ##]
nqed.

nlet rec fold_right_neList2 (T1,T2:Type) (f:T1 → T1 → T2 → T2) (acc:T2) (l1:ne_list T1) on l1 ≝
 match l1
  return λl1.Πl2.len_neList T1 l1 = len_neList T1 l2 → T2
 with
  [ ne_nil h ⇒ λl2.match l2 return λl2.len_neList T1 «£h» = len_neList T1 l2 → T2 with
   [ ne_nil h' ⇒ λp:len_neList T1 «£h» = len_neList T1 «£h'».
    f h h' acc
   | ne_cons h' t' ⇒ λp:len_neList T1 «£h» = len_neList T1 (h'§§t').
    False_rect_Type0 ? (fold_right_neList2_aux1 T1 h h' t' p)
   ]
  | ne_cons h t ⇒ λl2.match l2 return λl2.len_neList T1 (h§§t) = len_neList T1 l2 → T2 with
   [ ne_nil h' ⇒ λp:len_neList T1 (h§§t) = len_neList T1 «£h'».
    False_rect_Type0 ? (fold_right_neList2_aux2 T1 h h' t p)
   | ne_cons h' t' ⇒ λp:len_neList T1 (h§§t) = len_neList T1 (h'§§t').
    f h h' (fold_right_neList2 T1 T2 f acc t t' (fold_right_neList2_aux3 T1 h h' t t' p))
   ]
  ].

nlet rec bfold_right_neList2 (T1:Type) (f:T1 → T1 → bool) (l1,l2:ne_list T1) on l1 ≝
 match l1 with
  [ ne_nil h ⇒ match l2 with
   [ ne_nil h' ⇒ f h h' | ne_cons h' t' ⇒ false ]
  | ne_cons h t ⇒ match l2 with
   [ ne_nil h' ⇒ false | ne_cons h' t' ⇒ (f h h') ⊗ (bfold_right_neList2 T1 f t t')
   ]
  ].

(* nth elem *)
nlet rec nth_neList (T:Type) (nl:ne_list T) (n:nat) on nl ≝
 match nl with
  [ ne_nil h ⇒ match n with
   [ O ⇒ Some ? h | S _ ⇒ None ? ]
  | ne_cons h t ⇒ match n with
   [ O ⇒ Some ? h | S n' ⇒ nth_neList T t n' ]
  ].

(* abs elem *)
ndefinition abs_neList_aux1 : ∀T:Type.∀h:T.∀n.((len_neList T («£h»)) > (S n)) = true → False.
 #T; #h; #n; nnormalize; #H; ndestruct (*napply (bool_destruct … H)*). nqed.

ndefinition abs_neList_aux2 : ∀T:Type.∀h:T.∀t:ne_list T.∀n.((len_neList T (h§§t)) > (S n) = true) → ((len_neList T t) > n) = true.
 #T; #h; #t; #n; nnormalize; #H; napply H. nqed.

nlet rec abs_neList (T:Type) (l:ne_list T) on l ≝
 match l
  return λl.Πn.(((len_neList T l) > n) = true) → T
 with
  [ ne_nil h ⇒ λn.
   match n
    return λn.(((len_neList T (ne_nil T h)) > n) = true) → T
   with
    [ O ⇒ λp:(((len_neList T (ne_nil T h)) > O) = true).h
    | S n' ⇒ λp:(((len_neList T (ne_nil T h)) > (S n')) = true).
     False_rect_Type0 ? (abs_neList_aux1 T h n' p)
    ]
  | ne_cons h t ⇒ λn.
   match n with
    [ O ⇒ λp:(((len_neList T (ne_cons T h t)) > O) = true).h
    | S n' ⇒ λp:(((len_neList T (ne_cons T h t)) > (S n')) = true).
     abs_neList T t n' (abs_neList_aux2 T h t n' p)
    ]
  ].

(* esempio: abs_neList ? « 1; 2; 3 £ 4 » 0 (refl_eq …) = 0. *)

(* conversione *)
nlet rec neList_to_list (T:Type) (nl:ne_list T) on nl : list T ≝
 match nl with [ ne_nil h ⇒ [h] | ne_cons h t ⇒ [h]@(neList_to_list T t) ].
