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

include "delayed_updating/syntax/path_root_le.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Destructions with path_root_le *******************************************)

lemma dbfs_des_in_comp_nrle (t1) (t2) (r) (s):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ⧸⊑ s →
      s ϵ t1 → s ϵ t2.
#t1 #t2 #r #s *
#p #b #q #n #Hr #Ht12 #Hns #Hs
lapply (pcxr_des_eq … Hr) -Hr #H0 destruct
@(subset_in_eq_repl_fwd ????? Ht12) -t2
/3 width=1 by fsubst_in_comp_false/
qed-.

lemma dbfs_des_pcxr_nrle (t1) (t2) (r) (s) (p) (b) (q) (n):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ⧸⊑ s →
      s ϵ 𝐑❨t1,p,b,q,n❩ → s ϵ 𝐑❨t2,p,b,q,n❩.
#t1 #t2 #r #s #p #b #q #n #Ht12 #Hnrs * #H1s #H2s
/3 width=5 by dbfs_des_in_comp_nrle, subset_and_in/
qed-.
