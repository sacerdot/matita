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

include "ground/xoa/and_4.ma".
include "delayed_updating/syntax/path_balanced_structure.ma".
include "delayed_updating/reduction/prototerm_x_redex.ma".

(* EXPLICIT β-REDEX POINTER *************************************************)

(* Main inversions **********************************************************)

theorem pxr_inj (r) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        r ϵ 𝐑❨p1,b1,q1,n1❩ → r ϵ 𝐑❨p2,b2,q2,n2❩ →
        ∧∧ p1 = p2 & b1 = b2 & q1 = q2 & n1 = n2.
#r #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
* #Hr #Hb1 #Hq1 * #H0 #Hb2 #Hq2 destruct
elim (eq_inv_list_lcons_bi ????? H0) -H0 #H2 #H1
lapply (eq_inv_d_bi … H2) -H2 #H2
lapply (eq_inv_nsucc_bi … H2) -H2 #H2 destruct
lapply (pcc_inj_L_sx … Hq2 … Hq1 H1) -Hq1 -Hq2 #H0 destruct
lapply (eq_inv_list_append_sx_bi … H1) -H1 #H1
elim (eq_inv_list_lcons_bi ????? H1) -H1 #_ #H1
lapply (path_eq_des_pAb_bi_pbc … Hb2 Hb1 H1) -Hb2 -Hb1 #H0 destruct
lapply (eq_inv_list_append_sx_bi … H1) -H1 #H destruct
/2 width=1 by and4_intro/
qed-.
