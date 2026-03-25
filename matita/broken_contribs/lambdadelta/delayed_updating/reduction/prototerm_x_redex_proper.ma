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

include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/reduction/prototerm_x_redex.ma".

(* EXPLICIT β-REDEX POINTER *************************************************)

(* Destructions with ppc ****************************************************)

lemma pxr_S_des_ppc (p1) (p2) (b2) (q1) (q2) (n2):
      (p1◖𝗦)●q1 ϵ 𝐑❨p2,b2,q2,n2❩ → q1 ϵ 𝐏.
#p1 #p2 #b2 #q1 #q2 #n2 #Hpq1 #H0 destruct
<list_append_empty_sx in Hpq1; #H0
lapply (pxr_des_eq … H0) -H0 #H0
/2 width=6 by path_neq_beta_rcons_S/
qed-.
