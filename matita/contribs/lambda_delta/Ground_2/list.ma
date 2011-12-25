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

include "Ground_2/arith.ma".
include "Ground_2/notation.ma".

(* LISTS ********************************************************************)

inductive list (A:Type[0]) : Type[0] :=
  | nil : list A
  | cons: A -> list A -> list A.

interpretation "nil (list)" 'Nil = (nil ?).

interpretation "cons (list)" 'Cons hd tl = (cons ? hd tl).

let rec all A (R:predicate A) (l:list A) on l ≝
  match l with
  [ nil        ⇒ True
  | cons hd tl ⇒ R hd ∧ all A R tl
  ].
