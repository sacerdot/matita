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

include "ground/subsets/subsets_finite.ma".
include "delayed_updating/syntax/path_listed.ma".
include "delayed_updating/syntax/prototerm_eq.ma".

(* PROTOTERM ****************************************************************)

(* Inversions with subsets_finite *******************************************)

lemma term_pt_append_inv_finite (t) (p):
      p●t ϵ 𝛀 → t ϵ 𝛀.
#t #p * #ss2 #Hss2
elim (in_inv_path_append_sn_listed p ss2) #ss1 #Hss1
@(subsets_finite_in … ss1) #q #Hq
/4 width=1 by pt_append_in/
qed-.

(* Constructions with subsets_finite ****************************************)

lemma term_pt_append_finite (t) (p):
      t ϵ 𝛀 → p●t ϵ 𝛀.
#t #p * #ss1 #Hss1
lapply (pt_append_le_repl … p Hss1) -Hss1 #Hss1
elim (in_path_append_sn_listed p ss1) #ss2 #Hss2
@(subsets_finite_in … ss2)
@(subset_le_trans … Hss1) -Hss1
#r * #q #Hq #H0 destruct
/2 width=1 by/
qed.

lemma term_grafted_finite (t) (p):
      t ϵ 𝛀 → ⋔[p]t ϵ 𝛀.
#t #p #Ht
@(term_pt_append_inv_finite … p)
@(subsets_finite_le_trans … Ht) -Ht //
qed.
