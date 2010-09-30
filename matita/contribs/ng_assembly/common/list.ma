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

include "common/theory.ma".

(* *************** *)
(* LISTE GENERICHE *)
(* *************** *)

ninductive list (A:Type) : Type ≝
  nil: list A
| cons: A → list A → list A.

nlet rec append A (l1: list A) l2 on l1 ≝
 match l1 with
  [ nil ⇒ l2
  | (cons hd tl) ⇒ cons A hd (append A tl l2) ].

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
interpretation "append" 'append l1 l2 = (append ? l1 l2).

(* ************** *)
(* NON-EMPTY LIST *)
(* ************** *)

(* lista non vuota *)
ninductive ne_list (A:Type) : Type ≝
  | ne_nil: A → ne_list A
  | ne_cons: A → ne_list A → ne_list A.

(* append *)
nlet rec ne_append (A:Type) (l1,l2:ne_list A) on l1 ≝
 match l1 with
  [ ne_nil hd ⇒ ne_cons A hd l2
  | ne_cons hd tl ⇒ ne_cons A hd (ne_append A tl l2) ].

notation "hvbox(hd break §§ tl)"
  right associative with precedence 46
  for @{'ne_cons $hd $tl}.

(* \laquo \raquo *)
notation "« list0 x sep ; break £ y break »"
  non associative with precedence 90
  for ${fold right @{'ne_nil $y } rec acc @{'ne_cons $x $acc}}.

notation "hvbox(l1 break & l2)"
  right associative with precedence 47
  for @{'ne_append $l1 $l2 }.

interpretation "ne_nil" 'ne_nil hd = (ne_nil ? hd).
interpretation "ne_cons" 'ne_cons hd tl = (ne_cons ? hd tl).
interpretation "ne_append" 'ne_append l1 l2 = (ne_append ? l1 l2).
