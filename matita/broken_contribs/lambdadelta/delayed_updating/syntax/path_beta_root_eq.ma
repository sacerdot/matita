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
include "delayed_updating/syntax/path_beta.ma".

(* PATHS FOR β-REDUCTION ****************************************************)

(* Inversions with path_root_eq *********************************************)

lemma path_nreq_side_p_beta (p) (b) (q) (q1) (q2) (n):
      (p◖𝗦)●q1 ⧸≚ 𝐫❨p,b,q,n❩●q2.
#p #b #q #q1 #q2 #n #H0
elim (path_req_inv_append … H0) -H0 #x1 #x2
<list_append_assoc <list_append_assoc #H0
/2 width=7 by path_neq_p_beta/
qed-.

lemma path_nreq_side_p_p3beta (p) (b) (q) (q1) (q2):
      (p◖𝗦)●q1 ⧸≚ 𝐫❨p,b,q❩●q2.
#p #b #q #q1 #q2 #H0
elim (path_req_inv_append … H0) -H0 #x1 #x2
<list_append_assoc <list_append_assoc #H0
/2 width=6 by path_neq_p_p3beta/
qed-.

lemma path_nreq_p_p3beta_side (p) (b) (q) (q1) (q2):
      (𝐫❨p,b,q❩●q1 ⧸≚ (p◖𝗦)●q2).
/3 width=6 by path_nreq_side_p_p3beta, path_req_sym/
qed-.
