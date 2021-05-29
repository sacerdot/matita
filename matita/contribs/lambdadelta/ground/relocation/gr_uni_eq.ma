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
include "ground/relocation/gr_tl_eq.ma".
include "ground/relocation/gr_uni.ma".

(* UNIFORM ELEMENTS FOR GENERIC RELOCATION MAPS *****************************)

(* Inversions with gr_eq ****************************************************)

(*** uni_inv_push_dx *)
lemma gr_eq_inv_uni_push (n) (g):  𝐮❨n❩ ≡ ⫯g → ∧∧ 𝟎 = n & 𝐢 ≡ g.
#n @(nat_ind_succ … n) -n 
[ /3 width=5 by gr_eq_inv_push_bi, conj/
| #n #_ #f <gr_uni_succ #H elim (gr_eq_inv_next_push … H) -H //
]
qed-.

(*** uni_inv_push_sn *)
lemma gr_eq_inv_push_uni (n) (g): ⫯g ≡ 𝐮❨n❩ → ∧∧ 𝟎 = n & 𝐢 ≡ g.
/3 width=1 by gr_eq_inv_uni_push, gr_eq_sym/ qed-.

(*** uni_inv_next_dx *)
lemma gr_eq_inv_uni_next (n) (g): 𝐮❨n❩ ≡ ↑g → ∧∧ 𝐮❨↓n❩ ≡ g & ↑↓n = n.
#n @(nat_ind_succ … n) -n
[ #g <gr_uni_zero <gr_id_unfold #H elim (gr_eq_inv_push_next … H) -H //
| #n #_ #g <gr_uni_succ /3 width=5 by gr_eq_inv_next_bi, conj/
]
qed-.

(*** uni_inv_next_sn *)
lemma gr_eq_inv_next_uni (n) (g): ↑g ≡ 𝐮❨n❩ → ∧∧ 𝐮❨↓n❩ ≡ g & ↑↓n = n.
/3 width=1 by gr_eq_inv_uni_next, gr_eq_sym/ qed-.

(* Inversions with gr_id and gr_eq ******************************************)

(*** uni_inv_id_dx *)
lemma gr_eq_inv_uni_id (n): 𝐮❨n❩ ≡ 𝐢 → 𝟎 = n.
#n <gr_id_unfold #H elim (gr_eq_inv_uni_push … H) -H //
qed-.

(*** uni_inv_id_sn *)
lemma gr_eq_inv_id_uni (n):  𝐢 ≡ 𝐮❨n❩ → 𝟎 = n.
/3 width=1 by gr_eq_inv_uni_id, gr_eq_sym/ qed-.
