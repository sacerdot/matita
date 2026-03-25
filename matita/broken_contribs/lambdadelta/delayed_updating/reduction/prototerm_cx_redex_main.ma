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
include "delayed_updating/reduction/prototerm_x_redex_main.ma".
include "delayed_updating/reduction/prototerm_cx_redex.ma".

(* COMPLETE EXPLICIT β-REDEX POINTER ****************************************)

(* Main destructions ********************************************************)

theorem ol_des_pcxr_bi (t) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        (𝐑❨t,p1,b1,q1,n1❩ ≬ 𝐑❨t,p2,b2,q2,n2❩) →
        ∧∧ p1 = p2 & b1 = b2 & q1 = q2 & n1 = n2.
#t #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 * #r
* #_ #H1r * #_ #H2r
/2 width=3 by pxr_inj/
qed-.
