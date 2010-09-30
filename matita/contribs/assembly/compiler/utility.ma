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
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "freescale/extra.ma".

(* ************** *)
(* Non-Empty List *)
(* ************** *)

(* lista non vuota *)
inductive ne_list (A:Type) : Type ≝
  | ne_nil: A → ne_list A
  | ne_cons: A → ne_list A → ne_list A.

(* append *)
let rec ne_append (A:Type) (l1,l2:ne_list A) on l1 ≝
 match l1 with
  [ ne_nil hd => ne_cons A hd l2
  | ne_cons hd tl => ne_cons A hd (ne_append A tl l2) ].

notation "hvbox(hd break §§ tl)"
  right associative with precedence 46
  for @{'ne_cons $hd $tl}.

notation "« list0 x sep ; break £ y break »"
  non associative with precedence 90
  for ${fold right @{'ne_nil $y } rec acc @{'ne_cons $x $acc}}.

notation "hvbox(l1 break & l2)"
  right associative with precedence 47
  for @{'ne_append $l1 $l2 }.

interpretation "ne_nil" 'ne_nil hd = (ne_nil ? hd).
interpretation "ne_cons" 'ne_cons hd tl = (ne_cons ? hd tl).
interpretation "ne_append" 'ne_append l1 l2 = (ne_append ? l1 l2).

(* ************ *)
(* List Utility *)
(* ************ *)

(* conversione *)
let rec neList_to_list (T:Type) (p_l:ne_list T) on p_l ≝
 match p_l with [ ne_nil h ⇒ [h] | ne_cons h t ⇒ [h]@neList_to_list T t ].

let rec list_to_neList (T:Type) (p_l:list T) on p_l ≝
 match p_l with [ nil ⇒ None (ne_list T) | cons h t ⇒ match list_to_neList T t with [ None ⇒ Some ? «£h» | Some t' ⇒ Some ? («£h»&t') ]].

(* listlen *)
let rec len_list (T:Type) (p_l:list T) on p_l ≝
 match p_l with [ nil ⇒ O | cons _ t ⇒ S (len_list T t) ].

let rec len_neList (T:Type) (p_l:ne_list T) on p_l ≝
 match p_l with [ ne_nil _ ⇒ 1 | ne_cons _ t ⇒ S (len_neList T t) ].

(* nth elem *)
let rec nth_list (T:Type) (l:list T) (n:nat) on l ≝
 match l with
  [ nil ⇒ None ?
  | cons h t ⇒ match n with
   [ O ⇒ Some ? h | S n' ⇒ nth_list T t n' ]
  ].

let rec nth_neList (T:Type) (l:ne_list T) (n:nat) on l ≝
 match l with
  [ ne_nil h ⇒ match n with
   [ O ⇒ Some ? h | S _ ⇒ None ? ]
  | ne_cons h t ⇒ match n with
   [ O ⇒ Some ? h | S n' ⇒ nth_neList T t n' ]
  ].

let rec abs_nth_neList (T:Type) (l:ne_list T) (n:nat) on l ≝
 match l with
  [ ne_nil h ⇒ h
  | ne_cons h t ⇒ match n with
   [ O ⇒ h | S n' ⇒ abs_nth_neList T t n' ]
  ].

(* reverse *)
let rec reverse_list_aux (T:Type) (lin:list T) (lout:list T) on lin ≝
 match lin with [ nil ⇒ lout | cons h t ⇒ reverse_list_aux T t (h::lout) ].

definition reverse_list ≝ λT:Type.λl:list T.reverse_list_aux T l (nil T).

let rec reverse_neList_aux (T:Type) (lin:ne_list T) (lout:ne_list T) on lin ≝
 match lin with [ ne_nil h ⇒ h§§lout | ne_cons h t ⇒ reverse_neList_aux T t (h§§lout) ].

definition reverse_neList ≝ λT:Type.λl:ne_list T.
 match l with
  [ ne_nil h ⇒ l
  | ne_cons h t ⇒ reverse_neList_aux T t (ne_nil T h)
  ].

(* getLast *)
definition get_last_list ≝
λT:Type.λl:list T.match reverse_list T l with
 [ nil ⇒ None ?
 | cons h _ ⇒ Some ? h ].

definition get_last_neList ≝
λT:Type.λl:ne_list T.match reverse_neList T l with
 [ ne_nil h ⇒ h
 | ne_cons h _ ⇒ h ].

(* cutLast *)
definition cut_last_list ≝
λT:Type.λl:list T.match reverse_list T l with
 [ nil ⇒ nil T
 | cons _ t ⇒ reverse_list T t ].

definition cut_last_neList ≝
λT:Type.λl:ne_list T.match reverse_neList T l with
 [ ne_nil h ⇒ ne_nil T h
 | ne_cons _ t ⇒ reverse_neList T t ].

(* getFirst *)
definition get_first_list ≝
λT:Type.λl:list T.match l with
 [ nil ⇒ None ?
 | cons h _ ⇒ Some ? h ].

definition get_first_neList ≝
λT:Type.λl:ne_list T.match l with
 [ ne_nil h ⇒ h
 | ne_cons h _ ⇒ h ].

(* cutFirst *)
definition cut_first_list ≝
λT:Type.λl:list T.match l with
 [ nil ⇒ nil T
 | cons _ t ⇒ t ].

definition cut_first_neList ≝
λT:Type.λl:ne_list T.match l with
 [ ne_nil h ⇒ ne_nil T h
 | ne_cons _ t ⇒ t ].

(* apply f *)
let rec apply_f_list (T1,T2:Type) (l:list T1) (f:T1 → T2) on l ≝
match l with
 [ nil ⇒ nil T2
 | cons h t ⇒ cons T2 (f h) (apply_f_list T1 T2 t f) ].

let rec apply_f_neList (T1,T2:Type) (l:ne_list T1) (f:T1 → T2) on l ≝
match l with
 [ ne_nil h ⇒ ne_nil T2 (f h)
 | ne_cons h t ⇒ ne_cons T2 (f h) (apply_f_neList T1 T2 t f) ].

(* fold right *)
definition fold_right_list ≝
λT1,T2:Type.λf:T1 → T2 → T2.λacc:T2.
 let rec aux (l:list T1) on l ≝
  match l with
   [ nil ⇒ acc
   | cons h t ⇒ f h (aux t)
   ] in
  aux.

definition fold_right_neList ≝
λT1,T2:Type.λf:T1 → T2 → T2.λacc:T2.
 let rec aux (nel:ne_list T1) on nel ≝
  match nel with
   [ ne_nil h ⇒ f h acc
   | ne_cons h t ⇒ f h (aux t)
   ] in
  aux.

(* vuota? *)
definition is_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ True | cons _ _ ⇒ False ].

definition isb_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ true | cons _ _ ⇒ false ].

lemma isbemptylist_to_isemptylist : ∀T,l.isb_empty_list T l = true → is_empty_list T l.
 unfold isb_empty_list;
 unfold is_empty_list;
 intros;
 elim l;
 [ normalize; autobatch |
   normalize; autobatch ]
qed.

definition isnot_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ False | cons _ _ ⇒ True ].

definition isnotb_empty_list ≝
λT:Type.λl:list T.match l with [ nil ⇒ false | cons _ _ ⇒ true ].

lemma isnotbemptylist_to_isnotemptylist : ∀T,l.isnotb_empty_list T l = true → isnot_empty_list T l.
 unfold isnotb_empty_list;
 unfold isnot_empty_list;
 intros;
 elim l;
 [ normalize; autobatch |
   normalize; autobatch ]
qed.

lemma isempty_to_eq : ∀T,l.isb_empty_list T l = true → l = [].
 do 2 intro;
 elim l 0;
 [ 1: intro; reflexivity
 | 2: intros; normalize in H1:(%); destruct H1
 ].
qed.

lemma eq_to_isempty : ∀T,l.l = [] → isb_empty_list T l = true.
 do 2 intro;
 elim l 0;
 [ 1: intro; reflexivity
 | 2: intros; destruct H1
 ]
qed. 

(* ******** *)
(* naturali *)
(* ******** *)

definition isZero ≝ λn:nat.match n with [ O ⇒ True | S _ ⇒ False ].

definition isZerob ≝ λn:nat.match n with [ O ⇒ true | S _ ⇒ false ].

lemma iszerob_to_iszero : ∀n.isZerob n = true → isZero n.
 unfold isZerob;
 unfold isZero;
 intros;
 elim n;
 [ normalize; autobatch |
   normalize; autobatch ]
qed.

definition ltb ≝ λn1,n2:nat.(leb n1 n2) ⊗ (⊖ (eqb n1 n2)).

definition geb ≝ λn1,n2:nat.(⊖ (leb n1 n2)) ⊕ (eqb n1 n2).

definition gtb ≝ λn1,n2:nat.⊖ (leb n1 n2).
