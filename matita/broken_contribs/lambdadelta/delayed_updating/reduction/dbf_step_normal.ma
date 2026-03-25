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

include "delayed_updating/reduction/prototerm_normal.ma".
include "delayed_updating/reduction/dbf_step_c_redex.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Inversions with tnf ******************************************************)

lemma dbfs_inv_tnf_sx (t1) (t2) (r):
      t1 ϵ 𝐍𝐅 → t1 ➡𝐝𝐛𝐟[r] t2 → ⊥.
#t1 #t2 #r #Ht1 #Ht12
/4 width=3 by dbfs_inv_pcr, subset_nin_inv_empty/
qed-.
