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

include "basic_2/unfold/tpss_lift.ma".
include "basic_2/reducibility/tpr_lift.ma".
include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Advanced properties ******************************************************)

lemma cpr_cdelta: ∀L,K,V1,W1,W2,i.
                  ⇩[0, i] L ≡ K. ⓓV1 → K ⊢ V1 ▶* [0, |L| - i - 1] W1 →
                  ⇧[0, i + 1] W1 ≡ W2 → L ⊢ #i ➡ W2.
#L #K #V1 #W1 #W2 #i #HLK #HVW1 #HW12
lapply (ldrop_fwd_ldrop2_length … HLK) #Hi
@ex2_1_intro [2: // | skip | @tpss_subst /width=6/ ] (**) (* /3 width=6/ is too slow *)
qed.

lemma cpr_abst: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀V,T1,T2.
                L.ⓛV ⊢ T1 ➡ T2 → L ⊢ ⓛV1. T1 ➡ ⓛV2. T2.
#L #V1 #V2 * #V0 #HV10 #HV02 #V #T1 #T2 * #T0 #HT10 #HT02
lapply (tpss_inv_S2 … HT02 L V ?) -HT02 // #HT02
lapply (tpss_lsubs_trans … HT02 (L.ⓛV2) ?) -HT02 /2 width=1/ #HT02
@(ex2_1_intro … (ⓛV0.T0)) /2 width=1/ (* explicit constructors *)
qed.

lemma cpr_beta: ∀L,V1,V2,W,T1,T2.
                L ⊢ V1 ➡ V2 → L.ⓛW ⊢ T1 ➡ T2 → L ⊢ ⓐV1.ⓛW.T1 ➡ ⓓV2.T2.
#L #V1 #V2 #W #T1 #T2 * #V #HV1 #HV2 * #T #HT1 #HT2
lapply (tpss_inv_S2 … HT2 L W ?) -HT2 // #HT2
lapply (tpss_lsubs_trans … HT2 (L.ⓓV2) ?) -HT2 /2 width=1/ #HT2
@(ex2_1_intro … (ⓓV.T)) /2 width=1/ (**) (* explicit constructor, /3/ is too slow *)
qed.

lemma cpr_beta_dx: ∀L,V1,V2,W,T1,T2.
                   V1 ➡ V2 → L.ⓛW ⊢ T1 ➡ T2 → L ⊢ ⓐV1.ⓛW.T1 ➡ ⓓV2.T2.
/3 width=1/ qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pr2_gen_lref *)
lemma cpr_inv_lref1: ∀L,T2,i. L ⊢ #i ➡ T2 →
                     T2 = #i ∨
                     ∃∃K,V1,T1. ⇩[0, i] L ≡ K. ⓓV1 &
                                K ⊢ V1 ▶* [0, |L| - i - 1] T1 &
                                ⇧[0, i + 1] T1 ≡ T2 &
                                i < |L|.
#L #T2 #i * #X #H
>(tpr_inv_atom1 … H) -H #H
elim (tpss_inv_lref1 … H) -H /2 width=1/
* /3 width=6/
qed-.

(* Basic_1: was pr2_gen_abbr *)
lemma cpr_inv_abbr1: ∀L,V1,T1,U2. L ⊢ ⓓV1. T1 ➡ U2 →
                     (∃∃V,V2,T2. V1 ➡ V & L ⊢ V ▶* [O, |L|] V2 &
                                 L. ⓓV ⊢ T1 ➡ T2 &
                                 U2 = ⓓV2. T2
                      ) ∨
                      ∃∃T2. L.ⓓV1 ⊢ T1 ➡ T2 & ⇧[0,1] U2 ≡ T2.
#L #V1 #T1 #Y * #X #H1 #H2
elim (tpr_inv_abbr1 … H1) -H1 *
[ #V #T #T0 #HV1 #HT1 #HT0 #H destruct
  elim (tpss_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT02 #H destruct
  lapply (tps_lsubs_trans … HT0 (L. ⓓV) ?) -HT0 /2 width=1/ #HT0
  lapply (tps_weak_all … HT0) -HT0 #HT0
  lapply (tpss_lsubs_trans … HT02 (L. ⓓV) ?) -HT02 /2 width=1/ #HT02
  lapply (tpss_weak_all … HT02) -HT02 #HT02
  lapply (tpss_strap2 … HT0 HT02) -T0 /4 width=7/
| #T2 #HT12 #HXT2
  elim (lift_total Y 0 1) #Z #HYZ
  lapply (tpss_lift_ge … H2 (L.ⓓV1) … HXT2 … HYZ) -X // /2 width=1/ #H
  lapply (cpr_intro … HT12 … H) -T2 /3 width=3/
]
qed-.

(* Basic_1: was: pr2_gen_abst *)
lemma cpr_inv_abst1: ∀L,V1,T1,U2. L ⊢ ⓛV1. T1 ➡ U2 → ∀I,W.
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 & L. ⓑ{I} W ⊢ T1 ➡ T2 & U2 = ⓛV2. T2.
#L #V1 #T1 #Y * #X #H1 #H2 #I #W
elim (tpr_inv_abst1 … H1) -H1 #V #T #HV1 #HT1 #H destruct
elim (tpss_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct
lapply (tpss_lsubs_trans … HT2 (L. ⓑ{I} W) ?) -HT2 /2 width=1/ /4 width=5/
qed-.

(* Basic_1: was pr2_gen_appl *)
lemma cpr_inv_appl1: ∀L,V1,U0,U2. L ⊢ ⓐV1. U0 ➡ U2 →
                     ∨∨ ∃∃V2,T2.            L ⊢ V1 ➡ V2 & L ⊢ U0 ➡ T2 &
                                            U2 = ⓐV2. T2
                      | ∃∃V2,W,T1,T2.       L ⊢ V1 ➡ V2 & L. ⓓV2 ⊢ T1 ➡ T2 &
                                            U0 = ⓛW. T1 &
                                            U2 = ⓓV2. T2
                      | ∃∃V2,V,W1,W2,T1,T2. L ⊢ V1 ➡ V2 & L ⊢ W1 ➡ W2 & L. ⓓW2 ⊢ T1 ➡ T2 &
                                            ⇧[0,1] V2 ≡ V &
                                            U0 = ⓓW1. T1 &
                                            U2 = ⓓW2. ⓐV. T2.
#L #V1 #U0 #Y * #X #H1 #H2
elim (tpr_inv_appl1 … H1) -H1 *
[ #V #U #HV1 #HU0 #H destruct
  elim (tpss_inv_flat1 … H2) -H2 #V2 #U2 #HV2 #HU2 #H destruct /4 width=5/
| #V #W #T0 #T #HV1 #HT0 #H #H1 destruct
  elim (tpss_inv_bind1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H destruct
  lapply (tpss_weak … HT2 0 (|L|+1) ? ?) -HT2 // /4 width=8/
| #V0 #V #W #W0 #T #T0 #HV10 #HW0 #HT0 #HV0 #H #H1 destruct
  elim (tpss_inv_bind1 … H2) -H2 #W2 #X #HW02 #HX #HY destruct
  elim (tpss_inv_flat1 … HX) -HX #V2 #T2 #HV2 #HT2 #H destruct
  elim (tpss_inv_lift1_ge … HV2 … HV0 ?) -V // [3: /2 width=1/ |2: skip ] #V <minus_plus_m_m
  lapply (tpss_weak … HT2 0 (|L|+1) ? ?) -HT2 // /4 width=12/
]
qed-.

(* Note: the main property of simple terms *)
lemma cpr_inv_appl1_simple: ∀L,V1,T1,U. L ⊢ ⓐV1. T1 ➡ U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ T1 ➡ T2 &
                                     U = ⓐV2. T2.
#L #V1 #T1 #U #H #HT1
elim (cpr_inv_appl1 … H) -H *
[ /2 width=5/
| #V2 #W #W1 #W2 #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #V2 #V #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.

(* Relocation properties ****************************************************)

(* Basic_1: was: pr2_lift *)
lemma cpr_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                K ⊢ T1 ➡ T2 → L ⊢ U1 ➡ U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 * #T #HT1 #HT2
elim (lift_total T d e) #U #HTU 
lapply (tpr_lift … HT1 … HTU1 … HTU) -T1 #HU1
elim (lt_or_ge (|K|) d) #HKd
[ lapply (tpss_lift_le … HT2 … HLK HTU … HTU2) -T2 -T -HLK [ /2 width=2/ | /3 width=4/ ]
| lapply (tpss_lift_be … HT2 … HLK HTU … HTU2) -T2 -T -HLK // /3 width=4/
]
qed.

(* Basic_1: was: pr2_gen_lift *)
lemma cpr_inv_lift1: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                     ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀U2. L ⊢ U1 ➡ U2 →
                     ∃∃T2. ⇧[d, e] T2 ≡ U2 & K ⊢ T1 ➡ T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #U2 * #U #HU1 #HU2
elim (tpr_inv_lift1 … HU1 … HTU1) -U1 #T #HTU #T1
elim (lt_or_ge (|L|) d) #HLd
[ elim (tpss_inv_lift1_le … HU2 … HLK … HTU ?) -U -HLK [ /5 width=4/ | /2 width=2/ ]
| elim (lt_or_ge (|L|) (d + e)) #HLde
  [ elim (tpss_inv_lift1_be_up … HU2 … HLK … HTU ? ?) -U -HLK // [ /5 width=4/ | /2 width=2/ ] 
  | elim (tpss_inv_lift1_be … HU2 … HLK … HTU ? ?) -U -HLK // /5 width=4/
  ]
]
qed.
