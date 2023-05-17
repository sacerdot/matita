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

(* ARITHMETICAL PROPERTIES FOR λδ-2B ****************************************)

lemma arith_l4 (m11) (m12) (m21) (m22):
               m21+m22-(m11+m12) = m21-m11-m12+(m22-(m11-m21)-(m12-(m21-m11))).
#m11 #m12 #m21 #m22 >nminus_plus_assoc
elim (nat_split_le_ge (m11+m12) m21) #Hm1121
[ lapply (nle_trans m11 ??? Hm1121) // #Hm121
  lapply (nle_minus_dx_dx … Hm1121) #Hm12211
  <nminus_plus_comm_23 // @eq_f2 //
  <(nle_inv_eq_zero_minus m11 ?) // <(nle_inv_eq_zero_minus m12 ?) //
| <(nle_inv_eq_zero_minus m21 ?) // <nplus_zero_sn <nminus_plus_assoc <nplus_comm
  elim (nat_split_le_ge m11 m21) #Hm121
  [ lapply (nle_minus_sn_dx … Hm1121) #Hm2112
    <(nle_inv_eq_zero_minus m11 ?) // >nplus_minus_assoc // >nminus_assoc_comm_23 //
  | <(nle_inv_eq_zero_minus m21 ?) // >nminus_assoc_comm_23 //
  ]
]
qed.

lemma arith_l3 (m) (n1) (n2): n1+n2-m = n1-m+(n2-(m-n1)).
// qed.

lemma arith_l2 (n1) (n2): ↑n2-n1 = 𝟏-n1+(n2-(n1-𝟏)).
#n1 #n2 <arith_l3 //
qed.

lemma arith_l1 (n): npos (𝟏) = 𝟏-n+(n-(n-𝟏)).
#n <arith_l2 //
qed.
