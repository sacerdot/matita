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
include "ground/relocation/p1/pr_tl_eq.ma".
include "ground/relocation/p1/pr_uni.ma".

(* UNIFORM ELEMENTS FOR PARTIAL RELOCATION MAPS *****************************)

(* Inversions with pr_eq ****************************************************)

(*** uni_inv_push_dx *)
lemma pr_eq_inv_uni_push (n) (g):  𝐮❨n❩ ≐ ⫯g → ∧∧ 𝟎 = n & 𝐢 ≐ g.
#n @(nat_ind_succ … n) -n 
[ /3 width=5 by pr_eq_inv_push_bi, conj/
| #n #_ #f <pr_uni_succ #H elim (pr_eq_inv_next_push … H) -H //
]
qed-.

(*** uni_inv_push_sn *)
lemma pr_eq_inv_push_uni (n) (g): ⫯g ≐ 𝐮❨n❩ → ∧∧ 𝟎 = n & 𝐢 ≐ g.
/3 width=1 by pr_eq_inv_uni_push, pr_eq_sym/ qed-.

(*** uni_inv_next_dx *)
lemma pr_eq_inv_uni_next (n) (g): 𝐮❨n❩ ≐ ↑g → ∧∧ 𝐮❨⫰n❩ ≐ g & (⁤↑⫰n) = n.
#n @(nat_ind_succ … n) -n
[ #g <pr_uni_zero <pr_id_unfold #H elim (pr_eq_inv_push_next … H) -H //
| #n #_ #g <pr_uni_succ /3 width=5 by pr_eq_inv_next_bi, conj/
]
qed-.

(*** uni_inv_next_sn *)
lemma pr_eq_inv_next_uni (n) (g): ↑g ≐ 𝐮❨n❩ → ∧∧ 𝐮❨⫰n❩ ≐ g & (⁤↑⫰n) = n.
/3 width=1 by pr_eq_inv_uni_next, pr_eq_sym/ qed-.

(* Inversions with pr_id and pr_eq ******************************************)

(*** uni_inv_id_dx *)
lemma pr_eq_inv_uni_id (n): 𝐮❨n❩ ≐ 𝐢 → 𝟎 = n.
#n <pr_id_unfold #H elim (pr_eq_inv_uni_push … H) -H //
qed-.

(*** uni_inv_id_sn *)
lemma pr_eq_inv_id_uni (n):  𝐢 ≐ 𝐮❨n❩ → 𝟎 = n.
/3 width=1 by pr_eq_inv_uni_id, pr_eq_sym/ qed-.
