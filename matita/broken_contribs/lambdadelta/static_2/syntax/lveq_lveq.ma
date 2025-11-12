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

include "static_2/syntax/lveq_length.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Main inversion lemmas ****************************************************)

theorem lveq_inv_bind: ∀K1,K2. K1 ≋ⓧ*[𝟎,𝟎] K2 →
                       ∀I1,I2,m1,m2. K1.ⓘ[I1] ≋ⓧ*[m1,m2] K2.ⓘ[I2] →
                       ∧∧ 𝟎 = m1 & 𝟎 = m2.
#K1 #K2 #HK #I1 #I2 #m1 #m2 #H
lapply (lveq_fwd_length_eq … HK) -HK #HK
elim (lveq_inj_length … H) -H /3 width=1 by conj/
qed-.

theorem lveq_inj: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                  ∀m1,m2. L1 ≋ⓧ*[m1,m2] L2 →
                  ∧∧ n1 = m1 & n2 = m2.
#L1 #L2 #n1 #n2 #Hn #m1 #m2 #Hm
elim (lveq_fwd_length … Hn) -Hn #H1 #H2 destruct
elim (lveq_fwd_length … Hm) -Hm #H1 #H2 destruct
/2 width=1 by conj/
qed-.

theorem lveq_inj_void_sn_ge: ∀K1,K2. |K2| ≤ |K1| →
                             ∀n1,n2. K1 ≋ⓧ*[n1,n2] K2 →
                             ∀m1,m2. K1.ⓧ ≋ⓧ*[m1,m2] K2 →
                             ∧∧ (⁤↑n1) = m1 & 𝟎 = m2 & 𝟎 = n2.
#L1 #L2 #HL #n1 #n2 #Hn #m1 #m2 #Hm
elim (lveq_fwd_length … Hn) -Hn #H1 #H2 destruct
elim (lveq_fwd_length … Hm) -Hm #H1 #H2 destruct
>length_bind <nminus_succ_dx
<(nminus_succ_sx … HL) <(nle_inv_eq_zero_minus … HL)
/2 width=1 by and3_intro/
qed-.

theorem lveq_inj_void_dx_le: ∀K1,K2. |K1| ≤ |K2| →
                             ∀n1,n2. K1 ≋ⓧ*[n1,n2] K2 →
                             ∀m1,m2. K1 ≋ⓧ*[m1,m2] K2.ⓧ →
                             ∧∧ (⁤↑n2) = m2 & 𝟎 = m1 & 𝟎 = n1.
/3 width=5 by lveq_inj_void_sn_ge, lveq_sym/ qed-. (* auto: 2x lveq_sym *)
