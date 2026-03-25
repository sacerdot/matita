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

include "delayed_updating/syntax/prototerm_beta.ma".
include "delayed_updating/syntax/preterm_root_eq.ma".
include "delayed_updating/reduction/prototerm_cx_redex.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Inversions with preterm **************************************************)

lemma term_in_comp_clear_root_slice_inv_pcxr (t) (r) (p1) (p2) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p1,b,q,n❩ → p2 ϵ ▵t →
      p2 ≚ r → p2 ⊑ r.
#t #r #p1 #p2 #b #q #n #Ht #Hr #Hp2 #H0
/3 width=9 by pcxr_des_r, path_req_inv_complete_head_sx/
qed-.

(* Destructions with preterm ************************************************)

lemma pcxr_des_side (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → p◖𝗦 ϵ ▵t.
#t #r #p #b #q #n #Ht #Hr
lapply (pcxr_des_n … Hr) -Hr #Hn
/3 width=4 by term_full_A_post, path_beta_pA_in_root/
qed-.

(* Main destructions with preterm *******************************************)

theorem path_rle_des_pcxr_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        r1 ⊑ r2 → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #Hr12
<(path_rle_inv_complete … Ht … Hr12) -Ht -Hr12
/2 width=5 by pcxr_des_r/
qed-.

theorem path_req_des_pcxr_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        r1 ≚ r2 → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #Hr12
<(path_req_inv_complete … Ht … Hr12) -Ht -Hr12
/2 width=5 by pcxr_des_r/
qed-.

theorem term_in_comp_clear_root_slice_inv_pcxr_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        p2◖𝗦 ≚ r1 → p2◖𝗦 ⊑ r1.
/3 width=13 by term_in_comp_clear_root_slice_inv_pcxr, pcxr_des_side/
qed-.
