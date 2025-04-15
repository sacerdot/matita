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
include "delayed_updating/syntax/path_le.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_xfocus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with xprc **************************************************)

lemma brxf_ol_sn (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → t ≬ 𝐅❨p,b,q❩.
#t #r #p #b #q #n #Hr
lapply (xprc_des_n … Hr) -Hr #Hn
<brxf_unfold
/2 width=3 by subset_ol_i/
qed.

(* Destructions with xprc ***************************************************)

lemma ol_des_clear_brxf_xprc_bi_le (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      ⓪𝐅❨p1,b1,q1❩ ≬ ⓪𝐅❨p2,b2,q2❩ →
      ∨∨ r1 ⊑ r2 | r2 ⊑ r1.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Hr1 #Hr2
* #sz * #s1 * #x1 #_ #H3 #H2 * #s2 * #x2 #_ #H1 #H0 destruct
lapply (xprc_des_r … Hr1) -Hr1 #Hr1
lapply (xprc_des_r … Hr2) -Hr2 #Hr2
<path_clear_append in H0; <path_clear_append in ⊢ (???%→?);
>Hr1 >Hr2 #H0 -t -p1 -p2 -b1 -b2 -q1 -q2 -n1 -n2
elim (eq_inv_list_append_bi … H0) -H0 * #y
[ #_ #H0 | #H0 #_ ] destruct
/3 width=1 by path_le_mk, or_introl, or_intror/
qed-.

lemma term_in_root_brxf_des_xprc (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      s ϵ ▵𝐅❨p,b,q❩ → r ϵ ⓪▵↑s.
#t #r #s #p #b #q #n #Hr #Hs
lapply (xprc_des_r … Hr) -Hr #Hr destruct
/3 width=1 by in_comp_term_clear, term_in_root_slice_sym/
qed-.
