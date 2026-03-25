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

include "delayed_updating/syntax/path_root_eq.ma".
include "delayed_updating/syntax/prototerm_beta.ma".
include "delayed_updating/reduction/prototerm_x_redex.ma".

(* EXPLICIT β-REDEX POINTER *************************************************)

(* Destructions with path_root_eq *******************************************)

lemma req_des_pxr_dx (s) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → s ≚ r → s ≚ p◖𝗔.
#s #r #p #b #q #n #Hr #Hsr
lapply (pxr_des_eq … Hr) -Hr #H0 destruct
/2 width=5 by path_req_weak/
qed-.

(* Inversions with path_root_eq *********************************************)

lemma pxr_nreq_side (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → p◖𝗦 ⧸≚ r.
#r #p #b #q #n #Hr #Heq
lapply (pxr_des_eq … Hr) -Hr #H0 destruct
elim (path_req_inv_append … Heq) -Heq #q1 #q2 #H0
/2 width=7 by path_neq_p_beta/
qed-.

(* Main inversions with path_root_eq ****************************************)

theorem pxr_inv_ol (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        r1 ϵ 𝐑❨p1,b1,q1,n1❩ → r2 ϵ 𝐑❨p2,b2,q2,n2❩ →
        p2◖𝗦 ≚ r1 → p1◖𝗦 ≚ r2 → ⊥.
#r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Hr1 #Hr2 #Hp21 #Hp12
lapply (req_des_pxr_dx … Hr1 Hp21) -r1 -b1 -q1 -n1 #Hp21
lapply (req_des_pxr_dx … Hr2 Hp12) -r2 -b2 -q2 -n2 #Hp12
lapply (path_req_inv_rcons_bi … Hp12 Hp21) -p1 -p2 #H0 destruct
qed-.
