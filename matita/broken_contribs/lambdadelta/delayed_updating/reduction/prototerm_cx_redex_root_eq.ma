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

include "delayed_updating/reduction/prototerm_x_redex_root_eq.ma".
include "delayed_updating/reduction/prototerm_cx_redex.ma".

(* COMPLETE EXPLICIT β-REDEX POINTER ****************************************)

(* Destructions with path_root_le *******************************************)

(* Note: was: pcxr_des_clear_slice *)
lemma pcxr_des_rle_dx (t) (r) (p1) (p2) (b1) (q1) (n1):
      r ϵ 𝐑❨t,p1,b1,q1,n1❩ → p2 ⊑ r →
      ∃∃q2. q2 ϵ ⋔[p2]t & p2●q2 = r.
#t #r #p1 #p2 #b1 #q1 #n1 #Hr #Hp2
/3 width=5 by pcxr_des_r, path_rle_inv_in_comp_dx/
qed-.

(* Inversions with path_root_eq *********************************************)

(* Note: was: rp_nin_root_side *)
lemma pcxr_nreq_side (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → p◖𝗦 ⧸≚ r.
#t #r #p #b #q #n * #_ #Hr #Heq
/2 width=7 by pxr_nreq_side/
qed-.
