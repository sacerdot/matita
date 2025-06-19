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

include "delayed_updating/syntax/prototerm_clear_ol_eq.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Constructions with term_clear ********************************************)

lemma term_in_comp_clear_root_slice_dec_xprc (t) (r) (p1) (p2) (b) (q) (n):
      r ϵ 𝐑❨t,p1,b,q,n❩ →
      Decidable (r ϵ ⓪▵↑p2).
#t #r #p1 #p2 #b #q #n #Hr
<(xprc_des_clear … Hr) -Hr
@term_in_comp_clear_bi_root_slice_dec
qed-.

lemma term_in_comp_clear_root_slice_xprc_gen (t) (r1) (p1) (p2) (x1:ℙ) (x2:ℙ) (b1) (q1) (n1):
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ →
      r1●⓪x1 = ⓪p2●⓪x2 → r1 ϵ ⓪▵↑p2.
#t #r1 #p1 #p2 #x1 #x2 #b1 #q1 #n1 #Hr1
<(xprc_des_clear … Hr1) -Hr1 #H0
/3 width=3 by term_ol_inv_clear_slice_bi, term_ol_clear_slice_bi_gen/
qed.

(* Inversions with term_clear ***********************************************)

lemma term_in_comp_clear_root_slice_inv_xprc_gen (t) (r1) (p1) (p2) (b1) (q1) (n1):
      r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ →
      r1 ϵ ⓪▵↑p2 →
      ∃∃x1:ℙ,x2:ℙ. r1●⓪x1 = ⓪p2●⓪x2.
#t #r1 #p1 #p2 #b1 #q1 #n1 #Hr1
<(xprc_des_clear … Hr1) -Hr1 #H0
/3 width=1 by term_ol_clear_slice_bi, term_ol_clear_slice_bi_inv_gen/
qed-.

(* Destructions with term_clear *********************************************)

lemma xprc_des_r_clear (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → r◖𝗱𝟎 ϵ ⓪t.
#t #r #p #b #q #n #Hr
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #H0 destruct
>(path_clear_d_dx … (⁤↑n))
/2 width=1 by in_comp_term_clear/
qed-.

lemma xprc_des_ol_pA_sn (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ → r ϵ t2 →
      (⓪↑(p◖𝗔)) ≬ t2.
#t1 #t2 #r #p #b #q #n #H1r #H2r
lapply (xprc_des_r … H1r) -H1r #H1r destruct
/3 width=3 by in_comp_term_clear, subset_ol_i/
qed-.
