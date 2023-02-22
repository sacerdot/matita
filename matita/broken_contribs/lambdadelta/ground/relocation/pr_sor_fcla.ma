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

include "ground/xoa/ex_3_1.ma".
include "ground/xoa/ex_4_2.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_le_max.ma".
include "ground/relocation/pr_fcla_eq.ma".
include "ground/relocation/pr_sor_isi.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_fcla ***********************************************)

(*** sor_fcla_ex *)
lemma pr_sor_fcla_bi:
      ∀f1,n1. 𝐂❨f1❩ ≘ n1 → ∀f2,n2. 𝐂❨f2❩ ≘ n2 →
      ∃∃f,n. f1 ⋓ f2 ≘ f & 𝐂❨f❩ ≘ n & (n1 ∨ n2) ≤ n & n ≤ n1 + n2.
#f1 #n1 #Hf1 elim Hf1 -f1 -n1 /3 width=6 by pr_sor_isi_sn, ex4_2_intro/
#f1 #n1 #Hf1 #IH #f2 #n2 * -f2 -n2 /3 width=6 by pr_fcla_push, pr_fcla_next, ex4_2_intro, pr_sor_isi_dx/
#f2 #n2 #Hf2 elim (IH … Hf2) -IH -Hf2 -Hf1 [2,4: #f #n <nplus_succ_dx ] (* * full auto fails *)
[ /3 width=7 by pr_fcla_next, pr_sor_push_next, nle_max_sn_succ_dx, nle_succ_bi, ex4_2_intro/
| /4 width=7 by pr_fcla_next, pr_sor_next_bi, nle_succ_dx, nle_succ_bi, ex4_2_intro/
| /3 width=7 by pr_fcla_push, pr_sor_push_bi, ex4_2_intro/
| /3 width=7 by pr_fcla_next, pr_sor_next_push, nle_max_sn_succ_sn, nle_succ_bi, ex4_2_intro/
]
qed-.

(* Destructions with pr_fcla ************************************************)

(*** sor_fcla *)
lemma pr_sor_inv_fcla_bi:
      ∀f1,n1. 𝐂❨f1❩ ≘ n1 → ∀f2,n2. 𝐂❨f2❩ ≘ n2 → ∀f. f1 ⋓ f2 ≘ f →
      ∃∃n. 𝐂❨f❩ ≘ n & (n1 ∨ n2) ≤ n & n ≤ n1 + n2.
#f1 #n1 #Hf1 #f2 #n2 #Hf2 #f #Hf elim (pr_sor_fcla_bi … Hf1 … Hf2) -Hf1 -Hf2
/4 width=6 by pr_sor_mono, pr_fcla_eq_repl_back, ex3_intro/
qed-.

(* Destructions with pr_fcla ************************************************)

(*** sor_fwd_fcla_sn_ex *)
lemma pr_sor_des_fcla_sn:
      ∀f,n. 𝐂❨f❩ ≘ n → ∀f1,f2. f1 ⋓ f2 ≘ f →
      ∃∃n1. 𝐂❨f1❩ ≘ n1 & n1 ≤ n.
#f #n #H elim H -f -n
[ /4 width=4 by pr_sor_des_isi_sn, pr_fcla_isi, ex2_intro/
| #f #n #_ #IH #f1 #f2 #H
  elim (pr_sor_inv_push … H) -H [ |*: // ] #g1 #g2 #Hf #H1 #H2 destruct
  elim (IH … Hf) -f /3 width=3 by pr_fcla_push, ex2_intro/
| #f #n #_ #IH #f1 #f2 #H
  elim (pr_sor_inv_next … H) -H [1,3,4: * |*: // ] #g1 #g2 #Hf #H1 #H2 destruct
  elim (IH … Hf) -f /3 width=3 by pr_fcla_push, pr_fcla_next, nle_succ_bi, nle_succ_dx, ex2_intro/
]
qed-.

(*** sor_fwd_fcla_dx_ex *)
lemma pr_sor_des_fcla_dx:
      ∀f,n. 𝐂❨f❩ ≘ n → ∀f1,f2. f1 ⋓ f2 ≘ f →
      ∃∃n2. 𝐂❨f2❩ ≘ n2 & n2 ≤ n.
/3 width=4 by pr_sor_des_fcla_sn, pr_sor_comm/ qed-.
