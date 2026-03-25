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
include "delayed_updating/syntax/path_root_eq.ma".
include "delayed_updating/reduction/prototerm_cx_redex.ma".
include "delayed_updating/reduction/prototerm_x_focus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with pcxr **************************************************)

lemma brxf_ol_sx (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → t ≬ 𝐅❨p,b,q,n❩.
#t #r #p #b #q #n #Hr
lapply (pcxr_des_n … Hr) -Hr #Hn
<brxf_unfold
/2 width=3 by subset_ol_i/
qed.

(* Destructions with pcxr ***************************************************)

lemma brxf_des_pcxr (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → s ϵ 𝐅❨p,b,q,n❩ → r ⊑ s.
#t #r #s #p #b #q #n #Hr #Hs
lapply (pcxr_des_eq … Hr) -Hr #H0 destruct //
qed-.

(* Note: was: term_in_root_brxf_des_pcxr *)
lemma root_brxf_des_pcxr (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      s ϵ ▵𝐅❨p,b,q,n❩ → s ≚ r.
#t #r #s #p #b #q #n #Hr #Hs
lapply (pcxr_des_eq … Hr) -Hr #H0 destruct
/3 width=1 by path_req_mk_in_root_slice, path_req_sym/
qed-.

lemma ol_des_brxf_pcxr_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (𝐅❨p1,b1,q1,n1❩ ≬ 𝐅❨p2,b2,q2,n2❩) →
      r1 ≚ r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Hr1 #Hr2
* #sz #H1 #H2
/3 width=9 by brxf_des_pcxr, path_rle_canc_dx/
qed-.
