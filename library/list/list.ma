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

set "baseuri" "cic:/matita/list/".
include "logic/equality.ma".
include "higher_order_defs/functions.ma".

inductive list (A:Set) : Set :=
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
  \forall A:Set.\forall l:list A.\forall a:A.
    a::l <> [].
  intros;
  unfold Not;
  intros;
  discriminate H.
qed.

let rec id_list A (l: list A) on l :=
  match l with
  [ nil => []
  | (cons hd tl) => hd :: id_list A tl ].

let rec append A (l1: list A) l2 on l1 :=
  match l1 with
  [ nil => l2
  | (cons hd tl) => hd :: append A tl l2 ].

definition tail := \lambda A:Set. \lambda l: list A.
  match l with
  [ nil => []
  | (cons hd tl) => tl].

interpretation "append" 'append l1 l2 = (cic:/matita/list/append.con _ l1 l2).

theorem append_nil: \forall A:Set.\forall l:list A.l @ [] = l.
  intros;
  elim l;
  [ reflexivity;
  | simplify;
    rewrite > H;
    reflexivity;
  ]
qed.

theorem associative_append: \forall A:Set.associative (list A) (append A).
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
  \forall A:Set.\forall l1,l2:list A.\forall a:A.
    a :: (l1 @ l2) = (a :: l1) @ l2.
  intros;
  reflexivity;
qed.

(*
theorem nil_append_nil_both:
  \forall A:Set.\forall l1,l2:list A.
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
