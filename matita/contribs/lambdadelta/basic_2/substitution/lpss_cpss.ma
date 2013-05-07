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

include "basic_2/grammar/lpx_sn_lpx_sn.ma".
include "basic_2/substitution/lpss_ldrop.ma".

(* SN PARALLEL SUBSTITUTION FOR LOCAL ENVIRONMENTS **************************)

(* Main properties on context-sensitive parallel substitution for terms *****)

theorem cpss_trans_lpss: lpx_sn_transitive cpss cpss.
#L1 #T1 @(f2_ind … fw … L1 T1) -L1 -T1 #n #IH #L1 * [|*]
[ #I #Hn #T #H1 #L2 #HL12 #T2 #HT2 destruct
  elim (cpss_inv_atom1 … H1) -H1
  [ #H destruct
    elim (cpss_inv_atom1 … HT2) -HT2
    [ #H destruct //
    | * #K2 #V #V2 #i #HLK2 #HV2 #HVT2 #H destruct
      elim (lpss_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
      elim (lpss_inv_pair2 … H) -H #K1 #V1 #HK12 #HV1 #H destruct
      lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) /3 width=9/
    ]
  | * #K1 #V1 #V #i #HLK1 #HV1 #HVT #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #W2 #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -W2 #HLK2
    elim (cpss_inv_lift1 … HT2 … HLK2 … HVT) -L2 -T
    lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) /3 width=9/
  ]
| #a #I #V1 #T1 #Hn #X1 #H1 #L2 #HL12 #X2 #H2
  elim (cpss_inv_bind1 … H1) -H1 #V #T #HV1 #HT1 #H destruct
  elim (cpss_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct /4 width=5/
| #I #V1 #T1 #Hn #X1 #H1 #L2 #HL12 #X2 #H2
  elim (cpss_inv_flat1 … H1) -H1 #V #T #HV1 #HT1 #H destruct
  elim (cpss_inv_flat1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct /3 width=5/
]
qed-.

(* Basic_1: was only: subst1_trans *)
theorem cpss_trans: ∀L. Transitive … (cpss L).
/2 width=5 by cpss_trans_lpss/ qed-.

(* Properties on context-sensitive parallel substitution for terms **********)

(* Basic_1: was only: subst1_subst1 *)
lemma lpss_cpss_trans: ∀L1,L2. L1 ⊢ ▶* L2 →
                       ∀T1,T2. L2 ⊢ T1 ▶* T2 → L1 ⊢ T1 ▶* T2.
/2 width=5 by cpss_trans_lpss/ qed-.
