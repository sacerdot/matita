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

include "basic_2/syntax/lenv_length.ma".
include "basic_2/syntax/lveq.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

lemma lveq_eq_ex: ∀L1,L2. |L1| = |L2| → ∃n. L1 ≋ⓧ*[n, n] L2.
#L1 elim L1 -L1
[ #Y2 #H >(length_inv_zero_sn … H) -Y2 /2 width=3 by lveq_atom, ex_intro/
| #K1 * [ * | #I1 #V1 ] #IH #Y2 #H
  elim (length_inv_succ_sn … H) -H * [1,3: * |*: #I2 #V2 ] #K2 #HK #H destruct 
  elim (IH … HK) -IH -HK #n #HK
  /4 width=3 by lveq_pair_sn, lveq_pair_dx, lveq_void_sn, lveq_void_dx, ex_intro/
]
qed-.

(* Forward lemmas with length for local environments ************************)

lemma lveq_fwd_length_le_sn: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 → n1 ≤ |L1|.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize
/2 width=1 by le_S_S/
qed-.

lemma lveq_fwd_length_le_dx: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 → n2 ≤ |L2|.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize
/2 width=1 by le_S_S/
qed-.

lemma lveq_fwd_length: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                       |L1| + n2 = |L2| + n1.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize
/2 width=2 by injective_plus_r/
qed-.

lemma lveq_fwd_length_eq: ∀L1,L2,n. L1 ≋ⓧ*[n, n] L2 → |L1| = |L2|.
/3 width=2 by lveq_fwd_length, injective_plus_l/ qed-.

lemma lveq_fwd_length_minus: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                             |L1| - n1 = |L2| - n2.
/3 width=3 by lveq_fwd_length, lveq_fwd_length_le_dx, lveq_fwd_length_le_sn, plus_to_minus_2/ qed-.

lemma lveq_inj_length: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                       |L1| = |L2| → n1 = n2.
#L1 #L2 #n1 #n2 #H #HL12
lapply (lveq_fwd_length … H) -H #H
/2 width=2 by injective_plus_l/
qed-.
(*
(* Inversion lemmas with length for local environments **********************)
                   
lemma lveq_inv_void_dx_length: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2.ⓧ → |L1| ≤ |L2| →
                               ∃∃m2. L1 ≋ ⓧ*[n1, m2] L2 & n2 = ⫯m2 & n1 ≤ m2.
#L1 #L2 #n1 #n2 #H #HL12
lapply (lveq_fwd_length … H) normalize >plus_n_Sm #H0
lapply (plus2_inv_le_sn … H0 HL12) -H0 -HL12 #H0
elim (le_inv_S1 … H0) -H0 #m2 #Hm2 #H0 destruct
/3 width=4 by lveq_inv_void_dx, ex3_intro/
qed-.
*)