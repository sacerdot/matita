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

include "ground/subsets/subset_ol.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Destructions with xprc and preterm ***************************************)

lemma brf_xprc_des_clear (t) (r) (s) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      s ϵ 𝐅❨t,p,b,q❩ → ⓪s = r◖𝗱𝟎.
#t #r #s #p #b #q #n #Ht #Hr #Hs
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #Hr destruct
lapply (term_le_and_sn_single_dx … Ht Hn) -Ht -Hn #H0
lapply (H0 … Hs) -H0 -Hs #Hs
lapply (subset_in_inv_single ??? Hs) -Hs #H0 destruct //
qed-.

lemma brf_ol_xprc_des_inj (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 →
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (𝐅❨t,p1,b1,q1❩ ≬ 𝐅❨t,p2,b2,q2❩) → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht #Hr1 #Hr2 * #s #H1s #H2s
lapply (brf_xprc_des_clear … Ht Hr1 H1s) -Hr1
lapply (brf_xprc_des_clear … Ht Hr2 H2s) -Hr2
#H2 >H2 -s -Ht #H0 destruct //
qed-.

(* Inversions with xprc and preterm *****************************************)

lemma brf_ninj_xprc_inv_nol (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 →
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      r1 ⧸= r2 → (𝐅❨t,p1,b1,q1❩ ⧸≬ 𝐅❨t,p2,b2,q2❩).
/3 width=13 by brf_ol_xprc_des_inj/
qed-.
