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

(* Main forward lemmas ******************************************************)

theorem lveq_fwd_inj_succ_zero: ∀L1,L2,n1. L1 ≋ⓧ*[⫯n1, 0] L2 →
                                ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 → ∃x1. ⫯x1 = m1.
#L1 #L2 #n1 #Hn #m1 #m2 #Hm
lapply (lveq_fwd_length … Hn) -Hn <plus_n_O #Hn
lapply (lveq_fwd_length … Hm) -Hm >Hn >associative_plus -Hn #Hm
lapply (injective_plus_r … Hm) -Hm
<plus_S1 /2 width=2 by ex_intro/
qed-.

theorem lveq_fwd_inj_zero_succ: ∀L1,L2,n2. L1 ≋ⓧ*[0, ⫯n2] L2 →
                                ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 → ∃x2. ⫯x2 = m2.
/4 width=6 by lveq_fwd_inj_succ_zero, lveq_sym/ qed-. (* auto: 2x lveq_sym *)

theorem lveq_fwd_inj_succ_sn: ∀L1,L2,n1,n2. L1 ≋ⓧ*[⫯n1, n2] L2 →
                              ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 →
                              ∨∨ ∃x. ⫯x = n2 | ∃x. ⫯x = m1.
#L1 #L2 #n1 * [2: #n2 ] /3 width=2 by ex_intro, or_introl/
#Hn #m1 #m2 #Hm @or_intror @lveq_fwd_inj_succ_zero /width=6 by/ (**) (* auto fails *)
qed-.

theorem lveq_fwd_inj_succ_dx: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, ⫯n2] L2 →
                              ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 →
                              ∨∨ ∃x. ⫯x = n1 | ∃x. ⫯x = m2.
/4 width=6 by lveq_fwd_inj_succ_sn, lveq_sym/ qed-. (* auto: 2x lveq_sym *) 

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

theorem lveq_inj: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1, n2] L2 →
                  ∀m1,m2. L1 ≋ⓧ*[m1, m2] L2 →
                  ∧∧ n1 = m1 & n2 = m2.
#L1 #L2 @(f2_ind ?? length2 ?? L1 L2) -L1 -L2
#x #IH * [2: #L1 #I1 ] * [2,4: #L2 #I2 ]
[ cases I1 -I1 [ * | #I1 #V1 ] cases I2 -I2 [1,3: * |*: #I2 #V2 ] ]
#Hx #n1 #n2 #Hn #m1 #m2 #Hm destruct
[ elim (lveq_fwd_void_void … Hn) * #x #H destruct
  elim (lveq_fwd_void_void … Hm) * #y #H destruct
  [ lapply (lveq_inv_void_succ_sn … Hn) -Hn #Hn
    lapply (lveq_inv_void_succ_sn … Hm) -Hm #Hm
    elim (IH … Hn … Hm) -IH -Hn -Hm // #H1 #H2 destruct
    /2 width=1 by conj/
  | elim (lveq_fwd_inj_succ_sn … Hn … Hm) * #z #H destruct
    [ lapply (lveq_inv_void_succ_dx … Hn) -Hn #Hn
      lapply (lveq_inv_void_succ_dx … Hm) -Hm #Hm
      elim (IH … Hn … Hm) -IH -Hn -Hm [2: normalize // ] #H1 #H2 destruct (**) (* avoid normalize *)
      /2 width=1 by conj/
    | lapply (lveq_inv_void_succ_sn … Hn) -Hn #Hn
      lapply (lveq_inv_void_succ_sn … Hm) -Hm #Hm
      elim (IH … Hn … Hm) -IH -Hn -Hm // #H1 #H2 destruct
      /2 width=1 by conj/
    ]
  | elim (lveq_fwd_inj_succ_dx … Hn … Hm) * #z #H destruct
    [ lapply (lveq_inv_void_succ_sn … Hn) -Hn #Hn
      lapply (lveq_inv_void_succ_sn … Hm) -Hm #Hm
      elim (IH … Hn … Hm) -IH -Hn -Hm // #H1 #H2 destruct
      /2 width=1 by conj/
    | lapply (lveq_inv_void_succ_dx … Hn) -Hn #Hn
      lapply (lveq_inv_void_succ_dx … Hm) -Hm #Hm
      elim (IH … Hn … Hm) -IH -Hn -Hm [2: normalize // ] #H1 #H2 destruct (**) (* avoid normalize *)
      /2 width=1 by conj/
    ]
  | lapply (lveq_inv_void_succ_dx … Hn) -Hn #Hn
    lapply (lveq_inv_void_succ_dx … Hm) -Hm #Hm
    elim (IH … Hn … Hm) -IH -Hn -Hm [2: normalize // ] #H1 #H2 destruct (**) (* avoid normalize *)
    /2 width=1 by conj/
  ]
| lapply (lveq_fwd_abst_bind_length_le … Hn) #HL
  elim (le_to_or_lt_eq … HL) -HL #HL
  [ elim (lveq_inv_void_dx_length … Hn) -Hn // #x1 #Hn #H #_ destruct
    elim (lveq_inv_void_dx_length … Hm) -Hm // #y1 #Hm #H #_ destruct
    elim (IH … Hn … Hm) -IH -Hn -Hm -HL [2: normalize // ] #H1 #H2 destruct (**) (* avoid normalize *)
    /2 width=1 by conj/
  | elim (lveq_eq_ex … HL) -HL #x #HL
    elim (lveq_inv_pair_sn … HL … Hn) -Hn #H1 #H2 destruct
    elim (lveq_inv_pair_sn … HL … Hm) -Hm #H1 #H2 destruct
    /2 width=1 by conj/
  ]
| lapply (lveq_fwd_bind_abst_length_le … Hn) #HL
  elim (le_to_or_lt_eq … HL) -HL #HL
  [ elim (lveq_inv_void_sn_length … Hn) -Hn // #x1 #Hn #H #_ destruct
    elim (lveq_inv_void_sn_length … Hm) -Hm // #y1 #Hm #H #_ destruct
    elim (IH … Hn … Hm) -IH -Hn -Hm -HL // #H1 #H2 destruct
    /2 width=1 by conj/
  | lapply (sym_eq ??? HL) -HL #HL
    elim (lveq_eq_ex … HL) -HL #x #HL
    elim (lveq_inv_pair_dx … HL … Hn) -Hn #H1 #H2 destruct
    elim (lveq_inv_pair_dx … HL … Hm) -Hm #H1 #H2 destruct
    /2 width=1 by conj/
  ]
| elim (lveq_inv_pair_pair… Hn) -Hn #x #_ #H1 #H2 destruct
  elim (lveq_inv_pair_pair… Hm) -Hm #y #_ #H1 #H2 destruct
  /2 width=1 by conj/
| elim (lveq_inv_atom_bind … Hn) -Hn #x #Hn #H1 #H2 destruct
  elim (lveq_inv_atom_bind … Hm) -Hm #y #Hm #H1 #H2 destruct
  elim (IH … Hn … Hm) -IH -Hn -Hm /2 width=1 by conj/
| elim (lveq_inv_bind_atom … Hn) -Hn #x #Hn #H1 #H2 destruct
  elim (lveq_inv_bind_atom … Hm) -Hm #y #Hm #H1 #H2 destruct
  elim (IH … Hn … Hm) -IH -Hn -Hm /2 width=1 by conj/
| elim (lveq_inv_atom_atom … Hn) -Hn #H1 #H2 destruct
  elim (lveq_inv_atom_atom … Hm) -Hm #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

theorem lveq_inj_void_sn: ∀K1,K2,n1,n2. K1 ≋ⓧ*[n1, n2] K2 →
                          ∀m1,m2. K1.ⓧ ≋ⓧ*[m1, m2] K2 →
                          ∧∧ ⫯n1 = m1 & n2 = m2.
/3 width=4 by lveq_inj, lveq_void_sn/ qed-.

theorem lveq_inj_void_dx: ∀K1,K2,n1,n2. K1 ≋ⓧ*[n1, n2] K2 →
                          ∀m1,m2. K1 ≋ⓧ*[m1, m2] K2.ⓧ →
                          ∧∧ n1 = m1 & ⫯n2 = m2.
/3 width=4 by lveq_inj, lveq_void_dx/ qed-.
