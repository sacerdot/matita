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
| list_nil : list A
| list_cons: A → list A → list A
.

interpretation
  "nil (lists)"
  'CircledE A = (list_nil A).

interpretation
  "cons (lists)"
  'OPlusRight A hd tl = (list_cons A hd tl).

rec definition list_all A (R:predicate A) (l:list A) on l ≝ match l with
[ list_nil        ⇒ ⊤
| list_cons hd tl ⇒ ∧∧ R hd & list_all A R tl
].
