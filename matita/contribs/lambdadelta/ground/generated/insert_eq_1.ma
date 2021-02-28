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

include "basics/relations.ma".

(* GENERATED LIBRARY ********************************************************)

lemma insert_eq_1 (T1) (a1) (Q1,Q2:predicate T1):
      (∀b1. Q1 b1 → a1 = b1 → Q2 b1) → Q1 a1 → Q2 a1.
/2 width=1 by/ qed-.
