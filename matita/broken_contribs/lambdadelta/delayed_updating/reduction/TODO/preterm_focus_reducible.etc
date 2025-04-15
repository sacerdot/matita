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

(* Constructions with xprc and preterm **************************************)

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
