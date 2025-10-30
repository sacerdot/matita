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

lemma insert_eq_2 (T1) (T2) (a1) (a2) (Q1,Q2:relation2 T1 T2):
      (∀b1,b2. Q1 b1 b2 → a1 = b1 → a2 = b2 → Q2 b1 b2) → Q1 a1 a2 → Q2 a1 a2.
/2 width=1 by/ qed-.
