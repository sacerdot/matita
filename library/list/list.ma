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


include "logic/equality.ma".
include "higher_order_defs/functions.ma".

inductive list (A:Type) : Type :=
  | nil: list A
  | cons: A -> list A -> list A.

notation "hvbox(hd break :: tl)"
  right associative with precedence 46
  for @{'cons $hd $tl}.

notation "[ list0 x sep ; ]"
  non associative with precedence 90
  for ${fold right @'nil rec acc @{'cons $x $acc}}.

notation "hvbox(l1 break @ l2)"
  right associative with precedence 47
  for @{'append $l1 $l2 }.

interpretation "nil" 'nil = (cic:/matita/list/list.ind#xpointer(1/1/1) _).
interpretation "cons" 'cons hd tl =
  (cic:/matita/list/list.ind#xpointer(1/1/2) _ hd tl).

(* theorem test_notation: [O; S O; S (S O)] = O :: S O :: S (S O) :: []. *)

theorem nil_cons:
  \forall A:Type.\forall l:list A.\forall a:A.
    a::l <> [].
  intros;
  unfold Not;
  intros;
  destruct H.
qed.

let rec id_list A (l: list A) on l :=
  match l with
  [ nil => []
  | (cons hd tl) => hd :: id_list A tl ].

let rec append A (l1: list A) l2 on l1 :=
  match l1 with
  [ nil => l2
  | (cons hd tl) => hd :: append A tl l2 ].

definition tail := \lambda A:Type. \lambda l: list A.
  match l with
  [ nil => []
  | (cons hd tl) => tl].

interpretation "append" 'append l1 l2 = (cic:/matita/list/append.con _ l1 l2).

theorem append_nil: \forall A:Type.\forall l:list A.l @ [] = l.
  intros;
  elim l;
  [ reflexivity;
  | simplify;
    rewrite > H;
    reflexivity;
  ]
qed.

theorem associative_append: \forall A:Type.associative (list A) (append A).
  intros; unfold; intros;
  elim x;
  [ simplify;
    reflexivity;
  | simplify;
    rewrite > H;
    reflexivity;
  ]
qed.

theorem cons_append_commute:
  \forall A:Type.\forall l1,l2:list A.\forall a:A.
    a :: (l1 @ l2) = (a :: l1) @ l2.
  intros;
  reflexivity;
qed.

inductive permutation (A:Type) : list A -> list A -> Prop \def
  | refl : \forall l:list A. permutation ? l l
  | swap : \forall l:list A. \forall x,y:A. 
              permutation ? (x :: y :: l) (y :: x :: l)
  | trans : \forall l1,l2,l3:list A.
              permutation ? l1 l2 -> permut1 ? l2 l3 -> permutation ? l1 l3
with permut1 : list A -> list A -> Prop \def
  | step : \forall l1,l2:list A. \forall x,y:A. 
      permut1 ? (l1 @ (x :: y :: l2)) (l1 @ (y :: x :: l2)).

include "nat/nat.ma".  
   
definition x1 \def S O.
definition x2 \def S x1.
definition x3 \def S x2.
   
theorem tmp : permutation nat (x1 :: x2 :: x3 :: []) (x1 :: x3 :: x2 :: []).
  apply (trans ? (x1 :: x2 :: x3 :: []) (x1 :: x2 :: x3 :: []) ?).
  apply refl.
  apply (step ? (x1::[]) [] x2 x3).
  qed. 


(*
theorem nil_append_nil_both:
  \forall A:Type.\forall l1,l2:list A.
    l1 @ l2 = [] \to l1 = [] \land l2 = [].
*)

(*
include "nat/nat.ma".

theorem test_notation: [O; S O; S (S O)] = O :: S O :: S (S O) :: []. 
reflexivity.
qed.

theorem test_append: [O;O;O;O;O;O] = [O;O;O] @ [O;O] @ [O].
simplify.
reflexivity.
qed.
*)

let rec nth (A:Type) l d n on n ≝
 match n with
  [ O ⇒
     match l with
      [ nil ⇒ d
      | cons (x : A) _ ⇒ x
      ]
  | S n' ⇒ nth A (tail ? l) d n'
  ].
