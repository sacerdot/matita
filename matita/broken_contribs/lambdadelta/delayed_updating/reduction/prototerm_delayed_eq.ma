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

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with term_le ***********************************************)

lemma term_le_root_bi_brd_slice (t) (p) (b) (q) (n):
      ▵𝐃❨t,p,b,q,n❩ ⊆ ▵↑𝐫❨p,⓪b,q,⁤↑(♭b+n)❩.
#t #p #b #q #n
/3 width=3 by term_root_le_repl, pt_append_slice/
qed.

(* Constructions with term_eq ***********************************************)

lemma brd_grafted_eq_repl_fwd (t1) (t2) (p) (b) (q) (n):
      (⋔[p◖𝗦]t1 ⇔ ⋔[p◖𝗦]t2) → 𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #p #b #q #n
/2 width=1 by pt_append_eq_repl_bi/
qed.

lemma brd_eq_repl_fwd (t1) (t2) (p) (b) (q) (n):
      t1 ⇔ t2 → 𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #p #b #q #n
/3 width=1 by brd_grafted_eq_repl_fwd, term_grafted_eq_repl/
qed.

lemma brd_append_p (t) (p1) (p2) (b) (q) (n):
      p2●(𝐫❨p1,⓪b,q,⁤↑(♭b+n)❩●⋔[(p2●p1)◖𝗦]t) ⇔ 𝐃❨t,p2●p1,b,q,n❩.
#t #p1 #p2 #b #q #n
<brd_unfold <path_beta_append_p //
qed.

lemma grafted_brd_append_p (t) (p1) (p2) (b) (q) (n):
      (𝐫❨p1,⓪b,q,⁤↑(♭b+n)❩)●⋔[(p2●p1)◖𝗦]t ⇔ ⋔[p2]𝐃❨t,p2●p1,b,q,n❩.
#t #p1 #p2 #b #q #n
@(subset_eq_trans … (term_grafted_eq_repl …))
[| @brd_append_p | skip ]
@term_grafted_pt_append
qed.

lemma brd_append_q (t) (p) (b) (q1) (q2) (n):
      (𝐫❨p,⓪b,q1❩)●(𝐫❨q2,⁤↑(♭b+n)❩●⋔[p◖𝗦]t) ⇔ 𝐃❨t,p,b,q1●q2,n❩.
#t #p #b #q1 #q2 #n
<brd_unfold <path_beta_append_q //
qed.

lemma grafted_brd_append_q (t) (p) (b) (q1) (q2) (n):
      (𝐫❨q2,⁤↑(♭b+n)❩)●⋔[p◖𝗦]t ⇔ ⋔[𝐫❨p,⓪b,q1❩]𝐃❨t,p,b,q1●q2,n❩.
#t #p #b #q1 #q2 #n
@(subset_eq_trans … (term_grafted_eq_repl …))
[| @brd_append_q | skip ]
@term_grafted_pt_append
qed.

lemma brd_fsubst_grafted_eq_repl_fwd (t1) (t2) (u) (v) (p) (b) (q) (n):
      ⬕[⋔[p◖𝗦]u←⋔[p◖𝗦]v]⋔[p◖𝗦]t1 ⇔ ⋔[p◖𝗦]t2 →
      ⬕[𝐃❨u,p,b,q,n❩←𝐃❨v,p,b,q,n❩]𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #u #v #p #b #q #n #H0
@(subset_eq_canc_sx … (fsubst_append …))
@pt_append_eq_repl_bi //
qed.

lemma brd_fsubst_false_eq_repl_fwd (t1) (t2) (u) (v) (p) (b) (q) (n):
      (p◖𝗦) ⧸ϵ ▵u → (p◖𝗦) ⧸ϵ ▵v → ⬕[u←v]t1 ⇔ t2 →
      (𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩).
#t1 #t2 #u #v #p #b #q #n #H1np #H2np #H0
lapply (term_grafted_eq_repl … (p◖𝗦) H0) -H0 #H0
lapply (subset_eq_trans … (grafted_fsubst_false … H1np H2np) … H0) -H0 -H1np -H2np #H0
/2 width=1 by brd_grafted_eq_repl_fwd/
qed.

lemma brd_fsubst_true_eq_repl_fwd (t1) (t2) (u) (v) (p) (b) (q) (n):
      (⋔[p◖𝗦]t1) ≬ ⋔[p◖𝗦]u → ⬕[u←v]t1 ⇔ t2 →
      ⬕[𝐃❨u,p,b,q,n❩←𝐃❨v,p,b,q,n❩]𝐃❨t1,p,b,q,n❩ ⇔ 𝐃❨t2,p,b,q,n❩.
#t1 #t2 #u #v #p #b #q #n #Htu #H0
lapply (term_grafted_eq_repl … (p◖𝗦) H0) -H0 #H0
lapply (subset_eq_trans … (grafted_fsubst_true … Htu) … H0) -H0 -Htu #H0
/2 width=1 by brd_fsubst_grafted_eq_repl_fwd/
qed.

(* Note: grafted_brd_full REPLACED by term_grafted_pt_append *)

(* Main constructions with term_eq ******************************************)

theorem brd_brd_append_p (t1) (t2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        (⋔[𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩]t2) ⇔ ⋔[p2◖𝗦]t1 →
        (𝐃❨t2,𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩●p1,b1,q1,n1❩) ⇔
        (𝐃❨𝐃❨t1,p2◖𝗦●p1,b1,q1,n1❩,p2,b2,q2,n2❩).
#t1 #t2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht12
@(subset_eq_canc_sx … (brd_append_p …))
@pt_append_eq_repl_bi [ // ]
@(subset_eq_trans ????? (grafted_brd_append_p …))
@pt_append_eq_repl_bi [ // ]
>(list_append_lcons_sx … (𝗦)) >(list_append_lcons_sx … (𝗦))
@subset_eq_repl [4,5: @(term_grafted_append …) |1,2: skip ]
/2 width=1 by term_grafted_eq_repl/
qed.

theorem brd_brd_append_q (t1) (t2) (p) (b1) (b2) (q11) (q12) (q2) (n1) (n2):
        (⋔[p◖𝗦]t1) ⇔ ⋔[p◖𝗦]t2 →
        (𝐃❨t1,p,b1,𝐫❨q11,⓪b2,q2,⁤↑(♭b2+n2)❩●q12,n1❩) ⇔
        (𝐃❨𝐃❨t2,p,b1,q11◖𝗦●q12,n1❩,𝐫❨p,⓪b1,q11❩,b2,q2,n2❩).
#t1 #t2 #p #b1 #b2 #q11 #q12 #q2 #n1 #n2 #Ht
@(subset_eq_canc_sx … (brd_append_q …)) >path_beta_swap_pq
@pt_append_eq_repl_bi [ // ]
@(subset_eq_trans … (pt_append_eq_repl_bi … Ht)) -Ht [ @refl | skip ]
@(subset_eq_trans … (grafted_brd_append_q …))
[| @term_grafted_eq_repl_bi [ // | @subset_eq_refl ]
qed-.
