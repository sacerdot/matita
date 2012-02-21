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

include "Basic_2/reducibility/cnf_lift.ma".
include "Basic_2/computation/acp.ma".
include "Basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Relocation properties ****************************************************)

(* Basic_1: was: sn3_lift *)
lemma csn_lift: ∀L2,L1,T1,d,e. L1 ⊢ ⬇* T1 →
                ∀T2. ⇩[d, e] L2 ≡ L1 → ⇧[d, e] T1 ≡ T2 → L2 ⊢ ⬇* T2.
#L2 #L1 #T1 #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL21 #HT12
@csn_intro #T #HLT2 #HT2
elim (cpr_inv_lift … HL21 … HT12 … HLT2) -HLT2 #T0 #HT0 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_mono … HT0 … HT12) in HT2; -T0 /2 width=1/
qed.

(* Basic_1: was: sn3_gen_lift *)
lemma csn_inv_lift: ∀L2,L1,T1,d,e. L1 ⊢ ⬇* T1 →
                    ∀T2. ⇩[d, e] L1 ≡ L2 → ⇧[d, e] T2 ≡ T1 → L2 ⊢ ⬇* T2.
#L2 #L1 #T1 #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL12 #HT21
@csn_intro #T #HLT2 #HT2
elim (lift_total T d e) #T0 #HT0
lapply (cpr_lift … HL12 … HT21 … HT0 HLT2) -HLT2 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_inj … HT0 … HT21) in HT2; -T0 /2 width=1/
qed.

(* Advanced properties ******************************************************)

lemma csn_acp: acp cpr (eq …) (csn …).
@mk_acp
[ /2 width=1/
| /2 width=3/
| /2 width=5/
| @cnf_lift
]
qed.

(* Basic_1: was: sn3_abbr *)
lemma csn_lref_abbr: ∀L,K,V,i. ⇩[0, i] L ≡ K. ⓓV → K ⊢ ⬇* V → L ⊢ ⬇* #i.
#L #K #V #i #HLK #HV
@csn_intro #X #H #Hi
elim (cpr_inv_lref1 … H) -H
[ #H destruct elim (Hi ?) //
| -Hi * #K0 #V0 #V1 #HLK0 #HV01 #HV1 #_
  lapply (ldrop_mono … HLK0 … HLK) -HLK #H destruct
  lapply (ldrop_fwd_ldrop2 … HLK0) -HLK0 #HLK
  @(csn_lift … HLK HV1) -HLK -HV1
  @(csn_cpr_trans … HV) -HV
  @(cpr_intro … HV01) -HV01 //
]
qed.

lemma csn_abst: ∀L,W. L ⊢ ⬇* W → ∀I,V,T. L. ⓑ{I} V ⊢ ⬇* T → L ⊢ ⬇* ⓛW. T.
#L #W #HW elim HW -W #W #_ #IHW #I #V #T #HT @(csn_ind … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpr_inv_abst1 … H1 I V) -H1
#W0 #T0 #HLW0 #HLT0 #H destruct
elim (eq_false_inv_tpair_sn … H2) -H2
[ /3 width=5/
| -HLW0 * #H destruct /3 width=1/
]
qed.

lemma csn_appl_simple: ∀L,V. L ⊢ ⬇* V → ∀T1.
                       (∀T2. L ⊢ T1 ➡ T2 → (T1 = T2 → False) → L ⊢ ⬇* ⓐV. T2) →
                       𝐒[T1] → L ⊢ ⬇* ⓐV. T1.
#L #V #H @(csn_ind … H) -V #V #_ #IHV #T1 #IHT1 #HT1
@csn_intro #X #H1 #H2
elim (cpr_inv_appl1_simple … H1 ?) // -H1
#V0 #T0 #HLV0 #HLT10 #H destruct
elim (eq_false_inv_tpair_dx … H2) -H2
[ -IHV -HT1 #HT10
  @(csn_cpr_trans … (ⓐV.T0)) /2 width=1/ -HLV0
  @IHT1 -IHT1 // /2 width=1/
| -HLT10 * #H #HV0 destruct
  @IHV -IHV // -HT1 /2 width=1/ -HV0
  #T2 #HLT02 #HT02
  @(csn_cpr_trans … (ⓐV.T2)) /2 width=1/ -HLV0
  @IHT1 -IHT1 // -HLT02 /2 width=1/
]
qed.
