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

include "ground/arith/nat_pred_succ.ma".
include "ground/relocation/pr_tl_eq.ma".
include "ground/relocation/pr_uni.ma".

(* UNIFORM ELEMENTS FOR PARTIAL RELOCATION MAPS *****************************)

(* Inversions with pr_eq ****************************************************)

(*** uni_inv_push_dx *)
lemma pr_eq_inv_uni_push (n) (g):  š®āØnā© ā ā«Æg ā ā§ā§ š = n & š¢ ā g.
#n @(nat_ind_succ ā¦ n) -n 
[ /3 width=5 by pr_eq_inv_push_bi, conj/
| #n #_ #f <pr_uni_succ #H elim (pr_eq_inv_next_push ā¦ H) -H //
]
qed-.

(*** uni_inv_push_sn *)
lemma pr_eq_inv_push_uni (n) (g): ā«Æg ā š®āØnā© ā ā§ā§ š = n & š¢ ā g.
/3 width=1 by pr_eq_inv_uni_push, pr_eq_sym/ qed-.

(*** uni_inv_next_dx *)
lemma pr_eq_inv_uni_next (n) (g): š®āØnā© ā āg ā ā§ā§ š®āØānā© ā g & āān = n.
#n @(nat_ind_succ ā¦ n) -n
[ #g <pr_uni_zero <pr_id_unfold #H elim (pr_eq_inv_push_next ā¦ H) -H //
| #n #_ #g <pr_uni_succ /3 width=5 by pr_eq_inv_next_bi, conj/
]
qed-.

(*** uni_inv_next_sn *)
lemma pr_eq_inv_next_uni (n) (g): āg ā š®āØnā© ā ā§ā§ š®āØānā© ā g & āān = n.
/3 width=1 by pr_eq_inv_uni_next, pr_eq_sym/ qed-.

(* Inversions with pr_id and pr_eq ******************************************)

(*** uni_inv_id_dx *)
lemma pr_eq_inv_uni_id (n): š®āØnā© ā š¢ ā š = n.
#n <pr_id_unfold #H elim (pr_eq_inv_uni_push ā¦ H) -H //
qed-.

(*** uni_inv_id_sn *)
lemma pr_eq_inv_id_uni (n):  š¢ ā š®āØnā© ā š = n.
/3 width=1 by pr_eq_inv_uni_id, pr_eq_sym/ qed-.
