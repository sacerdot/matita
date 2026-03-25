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

include "ground/subsets/subset_listed_1.ma".
include "delayed_updating/syntax/prototerm_clear_listed.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subset_single and subset_le ***************************)

lemma term_clear_single_ge (p):
      ❴⓪p❵ ⊆ ⓪❴p❵.
/2 width=1 by term_clear_listed_ge/
qed.

lemma term_clear_single_le (p):
      (⓪❴p❵) ⊆ ❴⓪p❵.
/2 width=1 by term_clear_listed_le/
qed.

(* Constructions with subset_single and subset_eq ***************************)

lemma term_clear_single_eq (p):
      ❴⓪p❵ ⇔ ⓪❴p❵.
/2 width=1 by term_clear_listed_eq/
qed.
