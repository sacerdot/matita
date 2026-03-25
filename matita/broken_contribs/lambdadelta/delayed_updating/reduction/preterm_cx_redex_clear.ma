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

include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_root_eq_clear.ma".
include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/syntax/preterm_root_eq_clear.ma".
include "delayed_updating/reduction/preterm_cx_redex.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Inversions with preterm and clear ****************************************)

lemma req_inv_clear_bi_side_pcxr (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 →
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (⓪(p2◖𝗦) ≚ ⓪r1) → p2◖𝗦 ≚ r1.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht #Hr1 #Hr2 #H0
@(path_req_in_root_inv_clear_bi … Ht … H0) -H0
[ @(pcxr_des_side … Ht … Hr2)
| /3 width=5 by pcxr_des_r, term_in_comp_root/
]
qed-.

(* Destructiond with preterm and clear **************************************)

lemma nreq_des_side_pcxr (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      p1◖𝗦 ⧸≚ r2 →
      p1◖𝗦 ⧸≚ 𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #Hnr2 #H0
@Hnr2 -Hnr2
lapply (path_req_clear_bi … H0) -H0
<(path_clear_beta_b … (⁤↑n2))
>(pcxr_des_eq … Hr2) #H0
@(path_req_in_root_inv_clear_bi … Ht … H0) -H0
[ /2 width=5 by pcxr_des_side/
| /3 width=5 by pcxr_des_r, term_in_comp_root/
]
qed-.
