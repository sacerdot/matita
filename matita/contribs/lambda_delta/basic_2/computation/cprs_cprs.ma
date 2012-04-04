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

include "basic_2/reducibility/cpr_lift.ma".
include "basic_2/reducibility/cpr_cpr.ma".
include "basic_2/reducibility/lcpr_cpr.ma".
include "basic_2/computation/cprs_lcpr.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Advanced properties ******************************************************)

lemma cprs_abst_dx: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀V,T1,T2.
                    L.ⓛV ⊢ T1 ➡* T2 → L ⊢ ⓛV1. T1 ➡* ⓛV2. T2.
#L #V1 #V2 #HV12 #V #T1 #T2 #HT12 @(cprs_ind … HT12) -T2
[ /3 width=2/
| /3 width=6 by cprs_strap1, cpr_abst/ (**) (* /3 width=6/ is too slow *)
]
qed.

lemma cprs_abbr1_dx: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L. ⓓV1 ⊢ T1 ➡* T2 →
                     L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cprs_ind_dx … HT12) -T1
[ /3 width=5/
| #T1 #T #HT1 #_ #IHT1
  @(cprs_strap2 … IHT1) -IHT1 /2 width=1/
]
qed.

lemma cpr_abbr1: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L. ⓓV1 ⊢ T1 ➡ T2 →
                 L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
/3 width=1/ qed.

lemma cpr_abbr2: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L. ⓓV2 ⊢ T1 ➡ T2 →
                 L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12
lapply (lcpr_cpr_trans (L. ⓓV1) … HT12) /2 width=1/
qed.

(* Basic_1: was: pr3_strip *)
lemma cprs_strip: ∀L,T1,T. L ⊢ T ➡* T1 → ∀T2. L ⊢ T ➡ T2 →
                  ∃∃T0. L ⊢ T1 ➡ T0 & L ⊢ T2 ➡* T0.
/3 width=3/ qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr3_gen_appl *)
lemma cprs_inv_appl1: ∀L,V1,T1,U2. L ⊢ ⓐV1. T1 ➡* U2 →
                      ∨∨ ∃∃V2,T2.     L ⊢ V1 ➡* V2 & L ⊢ T1 ➡* T2 &
                                      U2 = ⓐV2. T2
                       | ∃∃V2,W,T.    L ⊢ V1 ➡* V2 &
                                      L ⊢ T1 ➡* ⓛW. T & L ⊢ ⓓV2. T ➡* U2
                       | ∃∃V0,V2,V,T. L ⊢ V1 ➡* V0 & ⇧[0,1] V0 ≡ V2 &
                                      L ⊢ T1 ➡* ⓓV. T & L ⊢ ⓓV. ⓐV2. T ➡* U2.
#L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5/
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpr_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5/
  | #V2 #W2 #T #T2 #HV02 #HT2 #H1 #H2 destruct /4 width=7/
  | #V #V2 #W0 #W2 #T #T2 #HV0 #HW02 #HT2 #HV2 #H1 #H2 destruct
    @or3_intro2 @(ex4_4_intro … HV2 HT10) /2 width=3/ /3 width=1/ (**) (* explicit constructor. /5 width=8/ is too slow because TC_transitive gets in the way *) 
  ]
| /4 width=8/
| /4 width=10/
]
qed-.

(* Main propertis ***********************************************************)

(* Basic_1: was: pr3_confluence *)
theorem cprs_conf: ∀L,T1,T. L ⊢ T ➡* T1 → ∀T2. L ⊢ T ➡* T2 →
                   ∃∃T0. L ⊢ T1 ➡* T0 & L ⊢ T2 ➡* T0.
/3 width=3/ qed.

(* Basic_1: was: pr3_t *)
theorem cprs_trans: ∀L,T1,T. L ⊢ T1 ➡* T → ∀T2. L ⊢ T ➡* T2 → L ⊢ T1 ➡* T2.
/2 width=3/ qed.

(* Basic_1: was: pr3_flat *)
lemma cprs_flat: ∀I,L,T1,T2. L ⊢ T1 ➡* T2 → ∀V1,V2. L ⊢ V1 ➡* V2 →
                 L ⊢ ⓕ{I} V1. T1 ➡* ⓕ{I} V2. T2.
#I #L #T1 #T2 #HT12 #V1 #V2 #HV12 @(cprs_ind … HV12) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1
@(cprs_trans … IHV1) -IHV1 /2 width=1/ 
qed.

lemma cprs_abst: ∀L,V1,V2. L ⊢ V1 ➡* V2 → ∀V,T1,T2.
                 L.ⓛV ⊢ T1 ➡* T2 → L ⊢ ⓛV1. T1 ➡* ⓛV2. T2.
#L #V1 #V2 #HV12 #V #T1 #T2 #HT12 @(cprs_ind … HV12) -V2
[ lapply (cprs_lsubs_conf … HT12 (L.ⓛV1) ?) -HT12 /2 width=2/
| #V0 #V2 #_ #HV02 #IHV01
  @(cprs_trans … IHV01) -V1 /2 width=2/
]
qed.

lemma cprs_abbr1: ∀L,V1,T1,T2. L. ⓓV1 ⊢ T1 ➡* T2 → ∀V2. L ⊢ V1 ➡* V2 →
                  L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
#L #V1 #T1 #T2 #HT12 #V2 #HV12 @(cprs_ind … HV12) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1
@(cprs_trans … IHV1) -IHV1 /2 width=1/
qed.

lemma cprs_abbr2_dx: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L. ⓓV2 ⊢ T1 ➡* T2 →
                     L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cprs_ind_dx … HT12) -T1
[ /2 width=1/
| #T1 #T #HT1 #_ #IHT1
  lapply (lcpr_cpr_trans (L. ⓓV1) … HT1) -HT1 /2 width=1/ #HT1
  @(cprs_trans … IHT1) -IHT1 /2 width=1/
]
qed.

lemma cprs_abbr2: ∀L,V1,V2. L ⊢ V1 ➡* V2 → ∀T1,T2. L. ⓓV2 ⊢ T1 ➡* T2 →
                  L ⊢ ⓓV1. T1 ➡* ⓓV2. T2.
#L #V1 #V2 #HV12 @(cprs_ind … HV12) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1 #T1 #T2 #HT12
lapply (IHV1 T1 T1 ?) -IHV1 // #HV1
@(cprs_trans … HV1) -HV1 /2 width=1/
qed.

(* Basic_1: was only: pr3_pr2_pr3_t pr3_wcpr0_t *)
lemma lcpr_cprs_trans: ∀L1,L2. L1 ⊢ ➡ L2 →
                       ∀T1,T2. L2 ⊢ T1 ➡* T2 → L1 ⊢ T1 ➡* T2.
#L1 #L2 #HL12 #T1 #T2 #H @(cprs_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT2
@(cprs_trans … IHT2) /2 width=3/
qed.
