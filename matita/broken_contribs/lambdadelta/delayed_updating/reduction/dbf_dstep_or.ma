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

include "delayed_updating/reduction/prototerm_dbf_residuals_or.ma".
include "delayed_updating/reduction/dbf_dstep.ma".

(* DELAYED BALANCED FOCUSED REDUCTION IN A DEVELOPMENT **********************)

(* Advanced constructions ***************************************************)

lemma dbfds_side_sx (t1) (t2) (r1) (p1) (p2) (b1) (b2) (q1) (q2) (n2) (n1) (x1) (x2):
      r1 ϵ 𝐑❨p1,b1,q1,n1❩ →
      p1◖𝗦 ⧸≚ 𝐫❨p2,b2,q2,n2❩ → p2◖𝗦●x1 = r1 →
      t1 ➡𝐝𝐛𝐟[r1] t2 →
      t1 Ꟈ➡𝐝𝐛𝐟[❴r1, 𝐫❨p2,b2,q2,n2❩●x2❵, ❴𝐫❨p2,b2,q2,n2❩●x2❵] t2.
#t1 #t2 #r1 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x1 #x2 #Hr1 #Hnr2 #H0 #Ht12
@(dbfds_mk … Ht12) -Ht12
/3 width=6 by term_dbfr_side_sx, subset_eq_sym/
qed.
