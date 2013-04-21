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

include "basic_2/static/aaa_lift.ma".
include "basic_2/static/lsuba_aaa.ma".
include "basic_2/reduction/lpr_ldrop.ma".

(* SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS *****************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_cpr_lpr_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A → ∀T2. L1 ⊢ T1 ➡ T2 →
                        ∀L2. L1 ⊢ ➡ L2 → L2 ⊢ T2 ⁝ A.
#L1 #T1 #A #H elim H -L1 -T1 -A
[ #L1 #k #X #H
  >(cpr_inv_sort1 … H) -H //
| #I #L1 #K1 #V1 #B #i #HLK1 #_ #IHV1 #X #H #L2 #HL12
  elim (cpr_inv_lref1 … H) -H
  [ #H destruct
    elim (lpr_ldrop_conf … HLK1 … HL12) -L1 #X #H #HLK2
    elim (lpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct /3 width=6/
  | * #Y #Z #V2 #H #HV12 #HV2
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    elim (lpr_ldrop_conf … HLK1 … HL12) -L1 #Z #H #HLK2
    elim (lpr_inv_pair1 … H) -H #K2 #V0 #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -V0 /3 width=7/
  ]
| #a #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpr_inv_abbr1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct /4 width=2/
  | #T2 #HT12 #HT2 #H destruct -IHV1
    @(aaa_inv_lift (L2.ⓓV1) … HT2) -HT2 /2 width=1/ /3 width=1/
  ]
| #a #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpr_inv_abst1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct /4 width=1/
| #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpr_inv_appl1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct /3 width=3/
  | #b #V2 #W1 #U1 #U2 #HV12 #HU12 #H1 #H2 destruct
    lapply (IHV1 … HV12 … HL12) -IHV1 -HV12 #HV2
    lapply (IHT1 (ⓛ{b}W1.U2) … HL12) -IHT1 /2 width=1/ -L1 #H
    elim (aaa_inv_abst … H) -H #B0 #A0 #HW1 #HU2 #H destruct
    lapply (lsuba_aaa_trans … HU2 (L2.ⓓV2) ?) -HU2 /2 width=2/ /2 width=3/
  | #b #V #V2 #W1 #W2 #U1 #U2 #HV1 #HV2 #HW12 #HU12 #H1 #H2 destruct
    lapply (aaa_lift L2 … B … (L2.ⓓW2) … HV2) -HV2 /2 width=1/ #HV2
    lapply (IHT1 (ⓓ{b}W2.U2) … HL12) -IHT1 /2 width=1/ -L1 #H
    elim (aaa_inv_abbr … H) -H /3 width=3/
  ]
| #L1 #V1 #T1 #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpr_inv_cast1 … H) -H
  [ * #V2 #T2 #HV12 #HT12 #H destruct /3 width=1/
  | -IHV1 /2 width=1/
  ]
]
qed-.

lemma aaa_cpr_conf: ∀L,T1,A. L ⊢ T1 ⁝ A → ∀T2. L ⊢ T1 ➡ T2 → L ⊢ T2 ⁝ A.
/2 width=5 by aaa_cpr_lpr_conf/ qed-.

lemma aaa_lpr_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. L1 ⊢ ➡ L2 → L2 ⊢ T ⁝ A.
/2 width=5 by aaa_cpr_lpr_conf/ qed-.
