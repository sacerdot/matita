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
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Advanced inversions ******************************************************)

lemma term_in_root_brd_inv_gen (t) (x) (p) (b) (q) (n):
      x ϵ ▵𝐃❨t,p,b,q,n❩ →
      ∃∃y,q0. x●y = 𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●q0 &
              (p◖𝗦)●q0 ϵ t.
#t #x #p #b #q #n #H0
lapply (term_ol_slice_sx … H0) -H0 * #z0 #H1z0 #H2z0
elim (term_in_slice_inv_gen … H1z0) -H1z0 #y #H0 destruct
elim (term_in_append_inv_gen … H2z0) -H2z0 #q0 #Hq0 #H0
/2 width=4 by ex2_2_intro/
qed-.

lemma nin_root_brd_side (t) (p) (b) (q1) (q2) (n):
      p◖𝗦●q1 ⧸ϵ ▵𝐃❨t,p,b,q2,n❩.
#t #p #b #q1 #q2 #n #H0
elim (term_in_root_brd_inv_gen … H0) -H0 #x #y
<list_append_assoc #H0 #_
/2 width=7 by path_neq_p_beta/
qed-.

lemma nin_root_brd_side_trunk (t) (p1) (b1) (b2) (q1) (q2) (n2):
      p1◖𝗦 ⧸ϵ ▵𝐃❨t,𝐫❨p1,b1,q1❩,b2,q2,n2❩.
#t #p1 #b1 #b2 #q1 #q2 #n2 #H0
elim (term_in_root_brd_inv_gen … H0) -H0 #x #y
<path_beta_swap_pq #H0 #_
@(path_neq_p_beta … H0)
qed-.
