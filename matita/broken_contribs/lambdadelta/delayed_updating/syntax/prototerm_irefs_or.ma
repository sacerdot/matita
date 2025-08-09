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

include "ground/subsets/subset_or_le.ma".
include "delayed_updating/syntax/prototerm_irefs_eq.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Constructions with subset_or and subset_le *******************************)

lemma subset_le_or_pirc (t1) (t2):
      (𝐈❨t1❩) ∪ 𝐈❨t2❩ ⊆ 𝐈❨t1 ∪ t2❩.
#t1 #t2
@subset_le_or_sn
@subset_le_pirc_bi // (**) (* auto fails *)
qed.

lemma subset_le_pirc_or (t1) (t2):
      (𝐈❨t1 ∪ t2❩) ⊆ 𝐈❨t1❩ ∪ 𝐈❨t2❩.
#t1 #t2 #r * #p #q #n #Hr #Hp * #Ht destruct
/3 width=4 by path_in_pirc, subset_or_in_sn, subset_or_in_dx/
qed.
