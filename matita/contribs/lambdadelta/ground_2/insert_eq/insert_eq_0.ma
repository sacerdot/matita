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

lemma insert_eq_0: ∀A,a. ∀Q1,Q2:predicate A. (∀a0. Q1 a0 → a = a0 → Q2 a0) → Q1 a → Q2 a.
/2 width=1 by/ qed-.
