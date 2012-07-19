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

include "basic_2/computation/cprs_lift.ma".
include "basic_2/computation/cprs_cprs.ma".
include "basic_2/conversion/cpc_cpc.ma".
include "basic_2/equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Advanced inversion lemmas ************************************************)

lemma cpcs_inv_cprs: ∀L,T1,T2. L ⊢ T1 ⬌* T2 →
                     ∃∃T. L ⊢ T1 ➡* T & L ⊢ T2 ➡* T.
#L #T1 #T2 #H @(cpcs_ind … H) -T2
[ /3 width=3/
| #T #T2 #_ #HT2 * #T0 #HT10 elim HT2 -HT2 #HT2 #HT0
  [ elim (cprs_strip … HT0 … HT2) -T #T #HT0 #HT2
    lapply (cprs_strap1 … HT10 … HT0) -T0 /2 width=3/
  | lapply (cprs_strap2 … HT2 … HT0) -T /2 width=3/
  ]
]
qed-.

(* Basic_1: was: pc3_gen_sort *)
lemma cpcs_inv_sort: ∀L,k1,k2. L ⊢ ⋆k1 ⬌* ⋆k2 → k1 = k2.
#L #k1 #k2 #H
elim (cpcs_inv_cprs … H) -H #T #H1
>(cprs_inv_sort1 … H1) -T #H2
lapply (cprs_inv_sort1 … H2) -L #H destruct //
qed-.

(* Basic_1: was: pc3_gen_sort_abst *)
lemma cpcs_inv_sort_abst: ∀L,W,T,k. L ⊢ ⋆k ⬌* ⓛW.T → ⊥.
#L #W #T #k #H
elim (cpcs_inv_cprs … H) -H #X #H1
>(cprs_inv_sort1 … H1) -X #H2
elim (cprs_inv_abst1 Abst W … H2) -H2 #W0 #T0 #_ #_ #H destruct
qed-.

(* Basic_1: was: pc3_gen_abst *)
lemma cpcs_inv_abst: ∀L,W1,W2,T1,T2. L ⊢ ⓛW1.T1 ⬌* ⓛW2.T2 → ∀I,V.
                     L ⊢ W1 ⬌* W2 ∧ L. ②{I}V ⊢ T1 ⬌* T2.
#L #W1 #W2 #T1 #T2 #H #I #V
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (cprs_inv_abst1 I V … H1) -H1 #W0 #T0 #HW10 #HT10 #H destruct
elim (cprs_inv_abst1 I V … H2) -H2 #W #T #HW2 #HT2 #H destruct /3 width=3/
qed-.

(* Basic_1: was: pc3_gen_abst_shift *)
lemma cpcs_inv_abst_shift: ∀L,W1,W2,T1,T2. L ⊢ ⓛW1.T1 ⬌* ⓛW2.T2 → ∀W.
                           L ⊢ W1 ⬌* W2 ∧ L. ⓛW ⊢ T1 ⬌* T2.
#L #W1 #W2 #T1 #T2 #H #W
lapply (cpcs_inv_abst … H Abst W) -H //
qed.

lemma cpcs_inv_abst1: ∀L,W1,T1,T. L ⊢ ⓛW1.T1 ⬌* T →
                      ∃∃W2,T2. L ⊢ T ➡* ⓛW2.T2 & L ⊢ ⓛW1.T1 ➡* ⓛW2.T2.
#L #W1 #T1 #T #H
elim (cpcs_inv_cprs … H) -H #X #H1 #H2
elim (cprs_inv_abst1 Abst W1 … H1) -H1 #W2 #T2 #HW12 #HT12 #H destruct
@(ex2_2_intro … H2) -H2 /2 width=2/ (**) (* explicit constructor, /3 width=6/ is slow *)
qed-.

lemma cpcs_inv_abst2: ∀L,W1,T1,T. L ⊢ T ⬌* ⓛW1.T1 →
                      ∃∃W2,T2. L ⊢ T ➡* ⓛW2.T2 & L ⊢ ⓛW1.T1 ➡* ⓛW2.T2.
/3 width=1 by cpcs_inv_abst1, cpcs_sym/ qed-.

(* Basic_1: was: pc3_gen_lift *)
lemma cpcs_inv_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                     ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                     L ⊢ U1 ⬌* U2 → K ⊢ T1 ⬌* T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 #HU12
elim (cpcs_inv_cprs … HU12) -HU12 #U #HU1 #HU2
elim (cprs_inv_lift1 … HLK … HTU1 … HU1) -U1 #T #HTU #HT1
elim (cprs_inv_lift1 … HLK … HTU2 … HU2) -L -U2 #X #HXU
>(lift_inj … HXU … HTU) -X -U -d -e /2 width=3/
qed-.

(* Advanced properties ******************************************************)

lemma cpr_cprs_conf: ∀L,T,T1,T2. L ⊢ T ➡* T1 → L ⊢ T ➡ T2 → L ⊢ T1 ⬌* T2.
#L #T #T1 #T2 #HT1 #HT2
elim (cprs_strip … HT1 … HT2) /2 width=3 by cpr_cprs_div/
qed-.

lemma cprs_cpr_conf: ∀L,T,T1,T2. L ⊢ T ➡* T1 → L ⊢ T ➡ T2 → L ⊢ T2 ⬌* T1.
#L #T #T1 #T2 #HT1 #HT2
elim (cprs_strip … HT1 … HT2) /2 width=3 by cprs_cpr_div/
qed-.

lemma cprs_conf: ∀L,T,T1,T2. L ⊢ T ➡* T1 → L ⊢ T ➡* T2 → L ⊢ T1 ⬌* T2.
#L #T #T1 #T2 #HT1 #HT2
elim (cprs_conf … HT1 … HT2) /2 width=3/
qed-.

(* Basic_1: was only: pc3_thin_dx *)
lemma cpcs_flat: ∀L,V1,V2. L ⊢ V1 ⬌* V2 → ∀T1,T2. L ⊢ T1 ⬌* T2 →
                 ∀I. L ⊢ ⓕ{I}V1. T1 ⬌* ⓕ{I}V2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12 #I
elim (cpcs_inv_cprs … HV12) -HV12 #V #HV1 #HV2
elim (cpcs_inv_cprs … HT12) -HT12 /3 width=5 by cprs_flat, cprs_div/ (**) (* /3 width=5/ is too slow *)
qed.

lemma cpcs_flat_dx_tpr_rev: ∀L,V1,V2. V2 ➡ V1 → ∀T1,T2. L ⊢ T1 ⬌* T2 →
                            ∀I. L ⊢ ⓕ{I}V1. T1 ⬌* ⓕ{I}V2. T2.
/3 width=1/ qed.

lemma cpcs_abst: ∀L,V1,V2. L ⊢ V1 ⬌* V2 →
                 ∀V,T1,T2. L.ⓛV ⊢ T1 ⬌* T2 → L ⊢ ⓛV1. T1 ⬌* ⓛV2. T2.
#L #V1 #V2 #HV12 #V #T1 #T2 #HT12
elim (cpcs_inv_cprs … HV12) -HV12
elim (cpcs_inv_cprs … HT12) -HT12
/3 width=6 by cprs_div, cprs_abst/ (**) (* /3 width=6/ is a bit slow *)
qed.

lemma cpcs_abbr_dx: ∀L,V,T1,T2. L.ⓓV ⊢ T1 ⬌* T2 → L ⊢ ⓓV. T1 ⬌* ⓓV. T2.
#L #V #T1 #T2 #HT12
elim (cpcs_inv_cprs … HT12) -HT12 /3 width=5 by cprs_div, cprs_abbr1/ (**) (* /3 width=5/ is a bit slow *)
qed.

lemma cpcs_bind_dx: ∀I,L,V,T1,T2. L.ⓑ{I}V ⊢ T1 ⬌* T2 →
                    L ⊢ ⓑ{I}V. T1 ⬌* ⓑ{I}V. T2.
* /2 width=1/ /2 width=2/ qed.

lemma cpcs_abbr_sn: ∀L,V1,V2,T. L ⊢ V1 ⬌* V2 → L ⊢ ⓓV1. T ⬌* ⓓV2. T.
#L #V1 #V2 #T #HV12
elim (cpcs_inv_cprs … HV12) -HV12 /3 width=5 by cprs_div, cprs_abbr1/ (**) (* /3 width=5/ is a bit slow *)
qed.

lemma cpcs_bind_sn: ∀I,L,V1,V2,T. L ⊢ V1 ⬌* V2 → L ⊢ ⓑ{I}V1. T ⬌* ⓑ{I}V2. T.
* /2 width=1/ /2 width=2/ qed.

lemma cpcs_beta_dx: ∀L,V1,V2,W,T1,T2.
                    L ⊢ V1 ➡ V2 → L.ⓛW ⊢ T1 ⬌* T2 → L ⊢ ⓐV1.ⓛW.T1 ⬌* ⓓV2.T2.
#L #V1 #V2 #W #T1 #T2 #HV12 #HT12
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
lapply (cprs_beta_dx … HV12 HT1) -HV12 -HT1 #HT1
lapply (cprs_lsubs_trans … HT2 (L.ⓓV2) ?) -HT2 /2 width=1/ #HT2
@(cprs_div … HT1) /2 width=1/
qed.

lemma cpcs_beta_dx_tpr_rev: ∀L,V1,V2,W,T1,T2.
                            V1 ➡ V2 → L.ⓛW ⊢ T2 ⬌* T1 →
                            L ⊢ ⓓV2.T2 ⬌* ⓐV1.ⓛW.T1.
/4 width=1/ qed.

(* Note: it does not hold replacing |L1| with |L2| *)
lemma cpcs_lsubs_trans: ∀L1,T1,T2. L1 ⊢ T1 ⬌* T2 →
                        ∀L2. L2 ≼ [0, |L1|] L1 → L2 ⊢ T1 ⬌* T2.
#L1 #T1 #T2 #HT12
elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_div, cprs_lsubs_trans/ (**) (* /3 width=5/ is a bit slow *)
qed.


(* Basic_1: was: pc3_lift *)
lemma cpcs_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                 ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                 K ⊢ T1 ⬌* T2 → L ⊢ U1 ⬌* U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 #HT12
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
elim (lift_total T d e) #U #HTU
lapply (cprs_lift … HLK … HTU1 … HT1 … HTU) -T1 #HU1
lapply (cprs_lift … HLK … HTU2 … HT2 … HTU) -K -T2 -T -d -e /2 width=3/
qed.

lemma cpcs_strip: ∀L,T1,T. L ⊢ T ⬌* T1 → ∀T2. L ⊢ T ⬌ T2 →
                  ∃∃T0. L ⊢ T1 ⬌ T0 & L ⊢ T2 ⬌* T0.
/3 width=3/ qed.

(* Main properties **********************************************************)

(* Basic_1: was pc3_t *)
theorem cpcs_trans: ∀L,T1,T. L ⊢ T1 ⬌* T → ∀T2. L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
/2 width=3/ qed.

theorem cpcs_canc_sn: ∀L,T,T1,T2. L ⊢ T ⬌* T1 → L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
/3 width=3 by cpcs_trans, cprs_comm/ qed. (**) (* /3 width=3/ is too slow *)

theorem cpcs_canc_dx: ∀L,T,T1,T2. L ⊢ T1 ⬌* T → L ⊢ T2 ⬌* T → L ⊢ T1 ⬌* T2.
/3 width=3 by cpcs_trans, cprs_comm/ qed. (**) (* /3 width=3/ is too slow *)

lemma cpcs_abbr1: ∀L,V1,V2. L ⊢ V1 ⬌* V2 → ∀T1,T2. L.ⓓV1 ⊢ T1 ⬌* T2 →
                  L ⊢ ⓓV1. T1 ⬌* ⓓV2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12
@(cpcs_trans … (ⓓV1.T2)) /2 width=1/
qed.

lemma cpcs_abbr2: ∀L,V1,V2. L ⊢ V1 ⬌* V2 → ∀T1,T2. L.ⓓV2 ⊢ T1 ⬌* T2 →
                  L ⊢ ⓓV1. T1 ⬌* ⓓV2. T2.
#L #V1 #V2 #HV12 #T1 #T2 #HT12
@(cpcs_trans … (ⓓV2.T1)) /2 width=1/
qed.
