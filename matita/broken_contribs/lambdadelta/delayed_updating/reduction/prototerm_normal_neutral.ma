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

include "delayed_updating/reduction/prototerm_neutral.ma".
include "delayed_updating/reduction/prototerm_normal.ma".

(* NORMAL FORM FOR PROTOTERM ************************************************)

(* Constructions with neutral path ******************************************)

(* UPDATE *)

lemma tnf_A_sn (t):
      t ⊆ 𝐍 → t ϵ 𝐍𝐅 → 𝗔◗t ϵ 𝐍𝐅.
#t #H1t #H2t #r * #p
@(list_ind_rcons … p) -p
[ #b #q #n * #_ #Hb #_
  <path_beta_unfold_dx <list_append_empty_dx #Hn (* ** UNFOLD *)
  elim (append_in_comp_inv_lcons_bi … Hn) -Hn #_ #H0
  elim (H1t … H0 …) -t //
| #p #l0 #_ #b #q #n * #Hr #Hb #Hq
  <path_beta_append_p #Hn
  elim (append_in_comp_inv_lcons_bi … Hn) -Hn #H0 #Hn destruct
  elim (tnf_inv_gen … (⓪𝐫❨p,b,q,⁤↑n❩) H2t) -H2t
  /2 width=3 by prc_mk_old/
]
qed.
