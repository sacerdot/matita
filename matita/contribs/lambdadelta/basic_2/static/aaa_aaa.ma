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

include "basic_2/substitution/ldrop_ldrop.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Main properties **********************************************************)

theorem aaa_mono: ∀L,T,A1. L ⊢ T ⁝ A1 → ∀A2. L ⊢ T ⁝ A2 → A1 = A2.
#L #T #A1 #H elim H -L -T -A1
[ #L #k #A2 #H
  >(aaa_inv_sort … H) -H //
| #I1 #L #K1 #V1 #B #i #HLK1 #_ #IHA1 #A2 #H
  elim (aaa_inv_lref … H) -H #I2 #K2 #V2 #HLK2 #HA2
  lapply (ldrop_mono … HLK1 … HLK2) -L #H destruct /2 width=1/
| #a #L #V #T #B1 #A1 #_ #_ #_ #IHA1 #A2 #H
  elim (aaa_inv_abbr … H) -H /2 width=1/
| #a #L #V1 #T1 #B1 #A1 #_ #_ #IHB1 #IHA1 #X #H
  elim (aaa_inv_abst … H) -H #B2 #A2 #HB2 #HA2 #H destruct /3 width=1/
| #L #V1 #T1 #B1 #A1 #_ #_ #_ #IHA1 #A2 #H
  elim (aaa_inv_appl … H) -H #B2 #_ #HA2
  lapply (IHA1 … HA2) -L #H destruct //
| #L #V #T #A1 #_ #_ #_ #IHA1 #A2 #H
  elim (aaa_inv_cast … H) -H /2 width=1/
]
qed-.