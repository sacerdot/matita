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

include "delayed_updating/reduction/subset_neutral.ma".
include "delayed_updating/reduction/prototerm_normal.ma".

(* NORMAL FORM FOR PROTOTERM ************************************************)

(* Constructions with neutral path ******************************************)

lemma tnf_A_sn (t):
      t ⊆ 𝐍 → t ϵ 𝐍𝐅 → 𝗔◗t ϵ 𝐍𝐅.
#t #H1t #H2t #r * #p
@(list_ind_rcons … p) -p
[ #b #q #n #_ #Hb #_
  <list_append_empty_dx >list_append_lcons_sn #Hn
  elim (append_in_comp_inv_lcons_bi … Hn) -Hn #_ #H0
  /4 width=6 by/
| #p #l0 #_ #b #q #n #Hr #Hb #Hq
  <list_append_rcons_dx >list_append_lcons_sn #Hn
  elim (append_in_comp_inv_lcons_bi … Hn) -Hn #H0 #Hn destruct
  elim (tnf_inv_gen … (⓪(p●𝗔◗b●𝗟◗q)) H2t) -H2t
  /2 width=3 by prc_mk/
]
qed.
