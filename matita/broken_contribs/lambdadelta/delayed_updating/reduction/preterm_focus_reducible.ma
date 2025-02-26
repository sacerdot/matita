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

include "ground/subsets/subset_ol_eq.ma".
include "ground/subsets/subset_listed_ol.ma".
include "delayed_updating/syntax/prototerm_clear_ol.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Destructions with xprc and preterm ***************************************)

lemma clear_brf_xprc_sx (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      ❴r◖𝗱𝟎❵ ⊆ ⓪𝐅❨t,p,b,q❩.
#t #r #p #b #q #n #Hr #s #Hs
lapply (subset_in_inv_single ??? Hs) -Hs #H0 destruct
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #Hr destruct
>(path_clear_d_dx … (⁤↑n)) <brf_unfold <brxf_unfold
/3 width=1 by in_comp_term_clear, subset_and_in/
qed-.

lemma clear_brf_xprc_dx (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      ⓪𝐅❨t,p,b,q❩ ⊆ ❴r◖𝗱𝟎❵.
#t #r #p #b #q #n #Ht #Hr #zs * #s #Hs #H0 destruct
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #Hr destruct
lapply (term_le_and_sn_single_dx … Ht Hn) -Ht -Hn #H0
lapply (H0 … Hs) -H0 -Hs #Hs
lapply (subset_in_inv_single ??? Hs) -Hs #H0 destruct //
qed-.

lemma clear_brf_xprc (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      ❴r◖𝗱𝟎❵ ⇔ ⓪𝐅❨t,p,b,q❩.
/3 width=8 by clear_brf_xprc_dx, clear_brf_xprc_sx, conj/
qed-.

lemma brf_ol_xprc_des_inj (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 →
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (𝐅❨t,p1,b1,q1❩ ≬ 𝐅❨t,p2,b2,q2❩) → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht #Hr1 #Hr2 #H0
lapply (clear_ol … H0) -H0 #H0
lapply (subset_ol_eq_repl … H0 ????)
[ @subset_eq_sym @(clear_brf_xprc … Hr2) // | skip
| @subset_eq_sym @(clear_brf_xprc … Hr1) // | skip
] -t -p1 -p2 -b1 -b2 -q1 -q2 -n1 -n2 #H0
lapply (subset_ol_inv_single_bi ??? H0) -H0 #H0 destruct //
qed-.

(* Inversions with xprc and preterm *****************************************)

lemma brf_ninj_xprc_inv_nol (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 →
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      r1 ⧸= r2 → (𝐅❨t,p1,b1,q1❩ ⧸≬ 𝐅❨t,p2,b2,q2❩).
/3 width=13 by brf_ol_xprc_des_inj/
qed-.
