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

include "basic_2/syntax/lveq_length.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Main inversion lemmas ****************************************************)

theorem lveq_inv_pair_sn: ∀K1,K2,n. K1 ≋ⓧ*[n, n] K2 →
                          ∀I1,I2,V,m1,m2. K1.ⓑ{I1}V ≋ⓧ*[m1, m2] K2.ⓘ{I2} →
                          ∧∧ 0 = m1 & 0 = m2.
#K1 #K2 #n #HK #I1 #I2 #V #m1 #m2 #H
lapply (lveq_fwd_length_eq … HK) -HK #HK
lapply (lveq_fwd_pair_sn … H) #H0 destruct
<(lveq_inj_length … H) -H normalize /3 width=1 by conj, eq_f/
qed-.

theorem lveq_inv_pair_dx: ∀K1,K2,n. K1 ≋ⓧ*[n, n] K2 →
                          ∀I1,I2,V,m1,m2. K1.ⓘ{I1} ≋ⓧ*[m1, m2] K2.ⓑ{I2}V →
                          ∧∧ 0 = m1 & 0 = m2.
/4 width=8 by lveq_inv_pair_sn, lveq_sym, commutative_and/ qed-.
(*
theorem lveq_inv_void_sn: ∀K1,K2,n1,n2. K1 ≋ⓧ*[n1, n2] K2 →
                          ∀m1,m2. K1.ⓧ ≋ⓧ*[m1, m2] K2 →
                          0 < m1. 
*)
(*
theorem lveq_inj: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                  ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 →
                  ∧∧ n1 = m1 & n2 = m2.
#L1 #L2 @(f2_ind ?? length2 ?? L1 L2) -L1 -L2
#x #IH #L1 #L2 #Hx #n1 #n2 #H
generalize in match Hx; -Hx
cases H -L1 -L2 -n1 -n2
/2 width=8 by lveq_inv_pair_dx, lveq_inv_pair_sn, lveq_inv_atom/
#K1 #K2 #n1 #n2 #HK #Hx #m1 #m2 #H destruct



[ #_ #m1 #m2 #HL -x /2 width=1 by lveq_inv_atom/
| #I1 #I2 #K1 #K2 #V1 #n #HK #_ #m1 #m2 #H -x     
  


theorem lveq_inj: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                  ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 →
                  ∧∧ n1 = m1 & n2 = m2.
#L1 #L2 #n1 #n2 #H @(lveq_ind_voids … H) -H -L1 -L2 -n1 -n2
[ #n1 #n2 #m1 #m2 #H elim (lveq_inv_voids … H) -H *
  [ /3 width=1 by voids_inj, conj/ ]
  #J1 #J2 #K1 #K2 #W #m #_ [ #H #_ | #_ #H ]
  elim (voids_inv_pair_sn … H) -H #H #_
  elim (voids_atom_inv … H) -H #H #_ destruct
]
#I1 #I2 #L1 #L2 #V #n1 #n2 #n #HL #IH #m1 #m2 #H
elim (lveq_inv_voids … H) -H *
[1,4: [ #H #_ | #_ #H ]
  elim (voids_inv_atom_sn … H) -H #H #_
  elim (voids_pair_inv … H) -H #H #_ destruct
]
#J1 #J2 #K1 #K2 #W #m #HK [1,3: #H1 #H2 |*: #H2 #H1 ]
elim (voids_inv_pair_sn … H1) -H1 #H #Hnm
[1,4: -IH -Hnm elim (voids_pair_inv … H) -H #H1 #H2 destruct
|2,3: elim (voids_inv_pair_dx … H2) -H2 #H2 #_
 
  elim (IH … HK)    


(*
/3 width=3 by lveq_inv_atom, lveq_inv_voids/
| 
  lapply (lveq_inv_voids … H) -H #H
  elim (lveq_inv_pair_sn … H) -H * /2 width=1 by conj/
  #Y2 #y2 #HY2 #H1 #H2 #H3 destruct 
*)

(*
fact lveq_inv_pair_bind_aux: ∀L1,L2,n1,n2. L1 ≋ ⓧ*[n1, n2] L2 →
                             ∀I1,I2,K1,K2,V1. K1.ⓑ{I1}V1 = L1 → K2.ⓘ{I2} = L2 →
                             ∨∨ ∃∃m. K1 ≋ ⓧ*[m, m] K2 & 0 = n1 & 0 = n2
                              | ∃∃m1,m2. K1 ≋ ⓧ*[m1, m2] K2 &
                                         BUnit Void = I2 & ⫯m2 = n2.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2
[ #J1 #J2 #L1 #L2 #V1 #H1 #H2 destruct
|2,3: #I1 #I2 #K1 #K2 #V #n #HK #_ #J1 #J2 #L1 #L2 #V1 #H1 #H2 destruct /3 width=2 by or_introl, ex3_intro/
|4,5: #K1 #K2 #n1 #n2 #HK #IH #J1 #J2 #L1 #L2 #V1 #H1 #H2 destruct
 /3 width=4 by _/
]
qed-.

lemma voids_inv_pair_bind: ∀I1,I2,K1,K2,V1,n1,n2. ⓧ*[n1]K1.ⓑ{I1}V1 ≋ ⓧ*[n2]K2.ⓘ{I2} →
                           ∨∨ ∃∃n. ⓧ*[n]K1 ≋ ⓧ*[n]K2 & 0 = n1 & 0 = n2
                            | ∃∃m2. ⓧ*[n1]K1.ⓑ{I1}V1 ≋ ⓧ*[m2]K2 &
                                    BUnit Void = I2 & ⫯m2 = n2.
/2 width=5 by voids_inv_pair_bind_aux/ qed-.

fact voids_inv_bind_pair_aux: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                              ∀I1,I2,K1,K2,V2. K1.ⓘ{I1} = L1 → K2.ⓑ{I2}V2 = L2 →
                              ∨∨ ∃∃n. ⓧ*[n]K1 ≋ ⓧ*[n]K2 & 0 = n1 & 0 = n2
                               | ∃∃m1. ⓧ*[m1]K1 ≋ ⓧ*[n2]K2.ⓑ{I2}V2 &
                                       BUnit Void = I1 & ⫯m1 = n1.
#L1 #L2 #n1 #n2 * -L1 -L2 -n1 -n2
[ #J1 #J2 #L1 #L2 #V1 #H1 #H2 destruct
|2,3: #I1 #I2 #K1 #K2 #V #n #HK #J1 #J2 #L1 #L2 #V2 #H1 #H2 destruct /3 width=2 by or_introl, ex3_intro/
|4,5: #K1 #K2 #n1 #n2 #HK #J1 #J2 #L1 #L2 #V2 #H1 #H2 destruct /3 width=3 by or_intror, ex3_intro/
]
qed-.

lemma voids_inv_bind_pair: ∀I1,I2,K1,K2,V2,n1,n2. ⓧ*[n1]K1.ⓘ{I1} ≋ ⓧ*[n2]K2.ⓑ{I2}V2 →
                           ∨∨ ∃∃n. ⓧ*[n]K1 ≋ ⓧ*[n]K2 & 0 = n1 & 0 = n2
                            | ∃∃m1. ⓧ*[m1]K1 ≋ ⓧ*[n2]K2.ⓑ{I2}V2 &
                                    BUnit Void = I1 & ⫯m1 = n1.
/2 width=5 by voids_inv_bind_pair_aux/ qed-.
*)
*)