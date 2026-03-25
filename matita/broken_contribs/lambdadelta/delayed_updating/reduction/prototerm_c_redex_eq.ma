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

include "ground/subsets/subset_eq.ma".
include "delayed_updating/reduction/prototerm_c_redex_le.ma".

(* COMPLETE β-REDEX POINTER *************************************************)

(* Constructions with subset_eq *********************************************)

lemma pcr_eq_repl (t1) (t2):
      t1 ⇔ t2 → 𝐑❨t1❩ ⇔ 𝐑❨t2❩.
#t1 #t2 * #Ht12 #Ht21
/3 width=3 by conj, pcr_le_repl/
qed.
