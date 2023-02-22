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

include "list/list.ma".
include "decidable_kit/eqtype.ma".
include "nat/plus.ma".

(* ### some functions on lists ### *)

definition count : ∀T : eqType.∀f : T → bool.∀l : list T. nat :=
  λT:eqType.λf,l. 
  foldr T nat (λx,acc. match (f x) with [ true ⇒ S acc | false ⇒ acc ]) O l.
     
let rec mem (d : eqType) (x : d) (l : list d) on l : bool ≝
  match l with
  [ nil ⇒ false 
  | cons y tl ⇒ orb (cmp d x y) (mem d x tl)].

(* ### eqtype for lists ### *)
let rec lcmp (d : eqType) (l1,l2 : list d) on l1 : bool ≝
  match l1 with
  [ nil ⇒ match l2 with [ nil ⇒ true | (cons _ _) ⇒ false]
  | (cons x1 tl1) ⇒ match l2 with 
      [ nil ⇒ false | (cons x2 tl2) ⇒ andb (cmp d x1 x2) (lcmp d tl1 tl2)]].
           
lemma lcmp_length : 
  ∀d:eqType.∀l1,l2:list d.
 lcmp ? l1 l2 = true → length ? l1 = length ? l2.
intros 2 (d l1); elim l1 1 (l2 x1);
[1: cases l2; simplify; intros; [reflexivity|destruct H] 
|2: intros 3 (tl1 IH l2); cases (l2); intros; [1:simplify in H; destruct H]
    simplify; (* XXX la apply non fa simplify? *) 
    apply congr_S; apply (IH l);
    (* XXX qualcosa di enorme e' rotto! la regola di convertibilita?! *)
    simplify in H; cases (b2pT ? ? (andbP ? ?) H); assumption]
qed.

lemma lcmpP : ∀d:eqType.∀l1,l2:list d. eq_compatible (list d) l1 l2 (lcmp d l1 l2).
intros (d l1 l2);
generalize in match (refl_eq ? (lcmp d l1 l2));
generalize in match (lcmp d l1 l2) in ⊢ (? ? ? % → %); intros 1 (c);
cases c; intros (H); [ apply reflect_true | apply reflect_false ]
[ lapply (lcmp_length ? ? ? H) as Hl;
  generalize in match H; clear H;
  apply (list_ind2 ? ? ? ? ? Hl); [1: intros; reflexivity]
  simplify; intros (tl1 tl2 hd1 hd2 IH H); cases (b2pT ? ? (andbP ? ?) H);
  rewrite > (IH H2); rewrite > (b2pT ? ? (eqP d ? ?) H1); reflexivity
| elim l1 in H l2 ⊢ % 1 (l1 x1);
   [ cases l1; simplify; [intros; destruct H | unfold Not; intros; destruct H1;]
   | intros 3 (tl1 IH l2); cases l2;
     [ unfold Not; intros; destruct H1;
     | simplify;  intros;
       cases (b2pT ? ? (andbPF ? ?) (p2bT ? ? (negbP ?) H)); clear H;
       [ intro; lapply (b2pF ? ? (eqP d ? ?) H1) as H'; clear H1;
         destruct H; apply H'; reflexivity;
       | intro; lapply (IH ? H1) as H'; destruct H;
         apply H'; reflexivity;]]]]
qed.
    
definition list_eqType : eqType → eqType ≝ λd:eqType.mk_eqType ? ? (lcmpP d).  
