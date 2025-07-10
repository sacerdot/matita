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

include "delayed_updating/syntax/prototerm_ol.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Advanced inversions ******************************************************)

lemma in_root_inv_brd (t) (x) (p) (b) (q) (n):
      x ϵ ▵𝐃❨t,p,b,q,n❩ →
      ∃∃y,q0. x●y = (p●𝗔◗(⓪b)●𝗟◗q)●𝗱(⁤↑(♭b+n))◗q0 &
              p◖𝗦●q0 ϵ t.
#t #x #p #b #q #n #H0
lapply (term_ol_slice_bi … H0) -H0 * #z0
* #y #_ #H1 * #z1 * #q0 #H2q0 #H2 #H3 destruct
/2 width=4 by ex2_2_intro/
qed-.

lemma nin_root_brd_side (t) (p) (b) (q1) (q2) (n):
      p●𝗦◗q1 ⧸ϵ ▵𝐃❨t,p,b,q2,n❩.
#t #p #b #q1 #q2 #n #H0
elim (in_root_inv_brd … H0) -H0 #x #y
<list_append_assoc <list_append_assoc
<list_append_assoc <list_append_assoc #H0 #_
lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed-.

lemma nin_root_brd_side_trunk (t) (p1) (p2) (b) (q) (n):
      p1◖𝗦 ⧸ϵ ▵𝐃❨t,p1●𝗔◗p2,b,q,n❩.
#t #p1 #p2 #b #q #n #H0
elim (in_root_inv_brd … H0) -H0 #x #y
>list_append_rcons_sn
<list_append_assoc <list_append_assoc
<list_append_assoc #H0
lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed-.
