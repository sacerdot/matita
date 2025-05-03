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

include "ground/arith/nat_le_minus_plus.ma".
include "static_2/syntax/lenv_length.ma".
include "static_2/syntax/lveq.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Properties with length for local environments ****************************)

lemma lveq_length_eq: ∀L1,L2. |L1| = |L2| → L1 ≋ⓧ*[𝟎,𝟎] L2.
#L1 elim L1 -L1
[ #Y2 #H >(length_inv_zero_sn … H) -Y2 /2 width=3 by lveq_atom, ex_intro/
| #K1 #I1 #IH #Y2 #H
  elim (length_inv_succ_sn … H) -H #I2 #K2 #HK #H destruct
  /3 width=1 by lveq_bind/
]
qed.

(* Forward lemmas with length for local environments ************************)

lemma lveq_fwd_length_le_sn: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 → n1 ≤ |L1|.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2
/2 width=1 by nle_succ_bi/
qed-.

lemma lveq_fwd_length_le_dx: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 → n2 ≤ |L2|.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2
/2 width=1 by nle_succ_bi/
qed-.

lemma lveq_fwd_length: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                       ∧∧ |L1|-|L2| = n1 & |L2|-|L1| = n2.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2
[ /2 width=1 by conj/
| #I1 #I2 #K1 #K2 #_ #IH >length_bind >length_bind //
]
#K1 #K2 #n #_ * #H1 #H2 destruct
>length_bind <nminus_succ_dx <nminus_succ_sn
/2 width=1 by nle_eq_zero_minus, conj/
qed-.

lemma lveq_length_fwd_sn: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 → |L1| ≤ |L2| → 𝟎 = n1.
#L1 #L2 #n1 #n2 #H #HL
elim (lveq_fwd_length … H) -H
>(nle_inv_eq_zero_minus … HL) //
qed-.

lemma lveq_length_fwd_dx: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 → |L2| ≤ |L1| → 𝟎 = n2.
#L1 #L2 #n1 #n2 #H #HL
elim (lveq_fwd_length … H) -H
>(nle_inv_eq_zero_minus … HL) //
qed-.

lemma lveq_inj_length: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                       |L1| = |L2| → ∧∧ 𝟎 = n1 & 𝟎 = n2.
#L1 #L2 #n1 #n2 #H #HL
elim (lveq_fwd_length … H) -H
>HL -HL /2 width=1 by conj/
qed-.

lemma lveq_fwd_length_plus: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                            |L1| + n2 = |L2| + n1.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 //
qed-.

lemma lveq_fwd_length_eq: ∀L1,L2. L1 ≋ⓧ*[𝟎,𝟎] L2 → |L1| = |L2|.
/3 width=2 by lveq_fwd_length_plus, eq_inv_nplus_bi_dx/ qed-.

lemma lveq_fwd_length_minus: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                             |L1| - n1 = |L2| - n2.
/3 width=3 by lveq_fwd_length_plus, lveq_fwd_length_le_dx, lveq_fwd_length_le_sn, nminus_plus_swap/ qed-.

lemma lveq_fwd_abst_bind_length_le: ∀I1,I2,L1,L2,V1,n1,n2.
                                    L1.ⓑ[I1]V1 ≋ⓧ*[n1,n2] L2.ⓘ[I2] → |L1| ≤ |L2|.
#I1 #I2 #L1 #L2 #V1 #n1 #n2 #HL
lapply (lveq_fwd_pair_sn … HL) #H destruct
elim (lveq_fwd_length … HL) -HL >length_bind >length_bind
<nminus_succ_bi <nminus_succ_bi //
qed-.

lemma lveq_fwd_bind_abst_length_le: ∀I1,I2,L1,L2,V2,n1,n2.
                                    L1.ⓘ[I1] ≋ⓧ*[n1,n2] L2.ⓑ[I2]V2 → |L2| ≤ |L1|.
/3 width=6 by lveq_fwd_abst_bind_length_le, lveq_sym/ qed-.

(* Inversion lemmas with length for local environments **********************)

(**) (* state with m2 ≝ ↓n2 *)
lemma lveq_inv_void_dx_length: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2.ⓧ → |L1| ≤ |L2| →
                               ∃∃m2. L1 ≋ ⓧ*[n1,m2] L2 & 𝟎 = n1 & (⁤↑m2) = n2.
#L1 #L2 #n1 #n2 #H #HL12
lapply (lveq_fwd_length_plus … H) >length_bind >nplus_succ_shift #H0
lapply (nplus_2_des_le_sn_sn … H0 HL12) -H0 -HL12 #H0
elim (nle_inv_succ_sn … H0) -H0 #_ #H0 >H0 in H; -H0 #H
elim (lveq_inv_void_succ_dx … H) -H /2 width=3 by ex3_intro/
qed-.

(**) (* state with m1 ≝ ↓n1 *)
lemma lveq_inv_void_sn_length: ∀L1,L2,n1,n2. L1.ⓧ ≋ⓧ*[n1,n2] L2 → |L2| ≤ |L1| →
                               ∃∃m1. L1 ≋ ⓧ*[m1,n2] L2 & (⁤↑m1) = n1 & 𝟎 = n2.
#L1 #L2 #n1 #n2 #H #HL
lapply (lveq_sym … H) -H #H
elim (lveq_inv_void_dx_length … H HL) -H -HL
/3 width=4 by lveq_sym, ex3_intro/
qed-.
