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

include "basic_2/reducibility/cif.ma".
include "basic_2/reducibility/cnf_lift.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

(* Main properties **********************************************************)

lemma tps_cif_eq: ∀L,T1,T2,d,e. L ⊢ T1 ▶[d, e] T2 → L ⊢ 𝐈⦃T1⦄ → T1 = T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e
[ //
| #L #K #V #W #i #d #e #_ #_ #HLK #_ #H -d -e
  elim (cif_inv_delta … HLK ?) //
| #L #a #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #H
  elim (cif_inv_bind … H) -H #HV1 #HT1 * #H destruct
  lapply (IHV12 … HV1) -IHV12 -HV1 #H destruct /3 width=1/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #H
  elim (cif_inv_flat … H) -H #HV1 #HT1 #_ #_ /3 width=1/
]
qed.

lemma tpss_cif_eq: ∀L,T1,T2,d,e. L ⊢ T1 ▶*[d, e] T2 → L ⊢ 𝐈⦃T1⦄ → T1 = T2.
#L #T1 #T2 #d #e #H @(tpss_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 #HT1
lapply (IHT1 HT1) -IHT1 #H destruct /2 width=5/
qed.

lemma tpr_cif_eq: ∀T1,T2. T1 ➡ T2 → ∀L. L ⊢ 𝐈⦃T1⦄ → T1 = T2.
#T1 #T2 #H elim H -T1 -T2
[ //
| * #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #L #H
  [ elim (cif_inv_appl … H) -H #HV1 #HT1 #_
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  | elim (cif_inv_ri2 … H) /2 width=1/
  ]
| #a #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #L #H
  elim (cif_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #a * #V1 #V2 #T1 #T #T2 #_ #_ #HT2 #IHV1 #IHT1 #L #H
  [ lapply (tps_lsubr_trans … HT2 (L.ⓓV2) ?) -HT2 /2 width=1/ #HT2
    elim (cif_inv_bind … H) -H #HV1 #HT1 * #H destruct
    lapply (IHV1 … HV1) -IHV1 -HV1 #H destruct
    lapply (IHT1 … HT1) -IHT1 #H destruct
    lapply (tps_cif_eq … HT2 ?) -HT2 //
  | <(tps_inv_refl_SO2 … HT2 ?) -HT2 //
    elim (cif_inv_ib2 … H) -H /2 width=1/ /3 width=2/
  ]
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #L #H
  elim (cif_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #V1 #T1 #T #T2 #_ #_ #_ #L #H
  elim (cif_inv_ri2 … H) /2 width=1/
| #V1 #T1 #T2 #_ #_ #L #H
  elim (cif_inv_ri2 … H) /2 width=1/
]
qed.

lemma cpr_cif_eq: ∀L,T1,T2. L ⊢ T1 ➡ T2 → L ⊢ 𝐈⦃T1⦄ → T1 = T2.
#L #T1 #T2 * #T0 #HT10 #HT02 #HT1
lapply (tpr_cif_eq … HT10 … HT1) -HT10 #H destruct /2 width=5/
qed.

theorem cif_cnf: ∀L,T. L ⊢ 𝐈⦃T⦄ → L ⊢ 𝐍⦃T⦄.
/3 width=3/ qed.

(* Note: this property is unusual *)
lemma cnf_crf_false: ∀L,T. L ⊢ 𝐑⦃T⦄ → L ⊢ 𝐍⦃T⦄ → ⊥.
#L #T #H elim H -L -T
[ #L #K #V #i #HLK #H
  elim (cnf_inv_delta … HLK H)
| #L #V #T #_ #IHV #H
  elim (cnf_inv_appl … H) -H /2 width=1/
| #L #V #T #_ #IHT #H
  elim (cnf_inv_appl … H) -H /2 width=1/
| #I #L #V #T * #H1 #H2 destruct
  [ elim (cnf_inv_zeta … H2)
  | elim (cnf_inv_tau … H2)
  ]
|5,6: #a * [ elim a ] #L #V #T * #H1 #_ #IH #H2 destruct
  [1,3: elim (cnf_inv_abbr … H2) -H2 /2 width=1/
  |*: elim (cnf_inv_abst … H2) -H2 /2 width=1/
  ]
| #a #L #V #W #T #H
  elim (cnf_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #a #L #V #W #T #H
  elim (cnf_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
]
qed.

theorem cnf_cif: ∀L,T. L ⊢ 𝐍⦃T⦄ → L ⊢ 𝐈⦃T⦄.
/2 width=4/ qed.
