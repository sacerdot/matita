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

include "ground/notation/functions/circledE_1.ma".
include "ground/notation/functions/oplusright_3.ma".
include "ground/lib/relations.ma".

(* LISTS ********************************************************************)

inductive list (A:Type[0]) : Type[0] :=
  | nil : list A
  | cons: A → list A → list A.

interpretation "nil (list)" 'CircledE A = (nil A).

interpretation "cons (list)" 'OPlusRight A hd tl = (cons A hd tl).

rec definition all A (R:predicate A) (l:list A) on l ≝
  match l with
  [ nil        ⇒ ⊤
  | cons hd tl ⇒ ∧∧ R hd & all A R tl
  ].
