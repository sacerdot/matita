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

include "delayed_updating/syntax/path_root_le_clear.ma".
include "delayed_updating/reduction/prototerm_x_focus_cx_redex.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Destructions with pcxr and clear *****************************************)

lemma clear_brxf_des_pcxr (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → s ϵ ⓪𝐅❨p,b,q,n❩ → ⓪r ⊑ s.
#t #r #s0 #p #b #q #n #Hr * #s #Hs #H0 destruct
/3 width=7 by brxf_des_pcxr, path_rle_clear_bi/
qed-.

lemma ol_des_clear_brxf_pcxr_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (⓪𝐅❨p1,b1,q1,n1❩ ≬ ⓪𝐅❨p2,b2,q2,n2❩) →
      (⓪r1 ≚ ⓪r2).
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Hr1 #Hr2
* #sz #H1 #H2
/3 width=9 by clear_brxf_des_pcxr, path_rle_canc_dx/
qed-.
