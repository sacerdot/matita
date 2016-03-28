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

include "basic_2/grammar/lenv.ma".

(* CONTEXT-SENSITIVE EQUIVALENCES FOR TERMS *********************************)

definition ceq: relation3 lenv term term ≝ λL,T1,T2. T1 = T2.

definition cfull: relation3 lenv term term ≝ λL,T1,T2. ⊤.

(* Basic properties *********************************************************)

lemma ceq_refl (L): reflexive … (ceq L).
// qed.

lemma cfull_refl (L): reflexive … (cfull L).
// qed.

lemma ceq_sym (L): symmetric … (ceq L).
// qed-.

lemma cfull_sym (L): symmetric … (cfull L).
// qed-.

lemma cfull_top (R:relation3 lenv term term) (L) (T1) (T2):
                R L T1 T2 → cfull L T1 T2.
// qed-.

lemma ceq_cfull (L) (T1) (T2): ceq L T1 T2 → cfull L T1 T2.
// qed.