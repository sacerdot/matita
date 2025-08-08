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

include "ground/subsets/subset_listed_le.ma".
include "delayed_updating/syntax/prototerm_ol.ma".
include "delayed_updating/reduction/prototerm_xfocus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Advanced inversions ******************************************************)

lemma nin_root_brxf_side (p) (b) (q1) (q2) (n):
      p◖𝗦●q1 ⧸ϵ ▵𝐅❨p,b,q2,n❩.
#p #b #q1 #q2 #n #H0
lapply (term_ol_slice_sx … H0) -H0 #H0
elim (term_ol_inv_slice_bi … H0) -H0 #y1 #y2
<list_append_assoc #H0
/2 width=7 by path_neq_p_beta/
qed-.

lemma nin_root_brxf_side_trunk (p1) (b1) (b2) (q1) (q2) (n2):
      p1◖𝗦 ⧸ϵ ▵𝐅❨𝐫❨p1,b1,q1❩,b2,q2,n2❩.
#p1 #b1 #b2 #q1 #q2 #n2 #H0
lapply (term_ol_slice_sx … H0) -H0 #H0
elim (term_ol_inv_slice_bi … H0) -H0 #y1 #y2
<path_beta_swap_pq #H0
@(path_neq_p_beta … H0)
qed-.

(* Constructions with subset_ol ****************************************)

lemma grafted_brxf_nol (p1) (p2) (b) (q) (n):
      ↑(p1◖𝗔) ⧸≬ ↑p2 →
      (Ⓕ) ⇔ ⋔[p2]𝐅❨p1,b,q,n❩.
#p1 #p2 #b #q #n #Hp12
@conj [ /2 width=1 by subset_empty_le_sn/ ] #x #Hx
elim (term_in_slice_inv_gen … Hx) -Hx #y #H0
elim Hp12 -Hp12
@(term_ol_slice_bi … (trans_eq … H0)) -H0
[2: <path_beta_unfold_b <list_append_assoc // | skip ] (* ** UNFOLD *)
qed.
