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

lemma pir_or_ge (t1) (t2):
      (𝐈❨t1❩) ∪ 𝐈❨t2❩ ⊆ 𝐈❨t1 ∪ t2❩.
#t1 #t2
@subset_le_or_sx
@subset_le_pir_bi // (**) (* auto fails *)
qed.

lemma pir_or_le (t1) (t2):
      (𝐈❨t1 ∪ t2❩) ⊆ 𝐈❨t1❩ ∪ 𝐈❨t2❩.
#t1 #t2 #r * #p #q #n #Hr #Hp * #Ht destruct
/3 width=4 by pir_mk, subset_or_in_sx, subset_or_in_dx/
qed.

(* Constructions with subset_or and subset_le *******************************)

lemma pir_or (t1) (t2):
      (𝐈❨t1❩) ∪ 𝐈❨t2❩ ⇔ 𝐈❨t1 ∪ t2❩.
/3 width=1 by conj, pir_or_ge, pir_or_le/
qed.
