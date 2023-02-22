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

include "logic/pts.ma".

ninductive list (A:Type[0]) : Type[0] ≝ 
  | nil: list A
  | cons: A -> list A -> list A.

notation "hvbox(hd break :: tl)"
  right associative with precedence 47
  for @{'cons $hd $tl}.

notation "[ list0 x sep ; ]"
  non associative with precedence 90
  for ${fold right @'nil rec acc @{'cons $x $acc}}.

notation "hvbox(l1 break @ l2)"
  right associative with precedence 47
  for @{'append $l1 $l2 }.

interpretation "nil" 'nil = (nil ?).
interpretation "cons" 'cons hd tl = (cons ? hd tl).

nlet rec append A (l1: list A) l2 on l1 ≝ 
  match l1 with
  [ nil ⇒ l2
  | cons hd tl ⇒ hd :: append A tl l2 ].

interpretation "append" 'append l1 l2 = (append ? l1 l2).

nlet rec id_list A (l: list A) on l ≝ 
  match l with
  [ nil ⇒ []
  | cons hd tl ⇒ hd :: id_list A tl ].


ndefinition tail ≝ λA:Type[0].λl:list A.
  match l with
  [ nil ⇒  []
  | cons hd tl ⇒  tl].

nlet rec flatten S (l : list (list S)) on l : list S ≝ 
match l with [ nil ⇒ [ ] | cons w tl ⇒ w @ flatten ? tl ].

