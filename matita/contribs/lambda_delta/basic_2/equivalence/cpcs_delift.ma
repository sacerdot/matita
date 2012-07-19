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

include "basic_2/unfold/delift_lift.ma".
include "basic_2/unfold/delift_delift.ma".
include "basic_2/computation/cprs_delift.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Advanced inversion lemmas ************************************************)

lemma cprs_inv_appl1_cpcs: ∀L,V1,T1,U2. L ⊢ ⓐV1. T1 ➡* U2 → (
                           ∃∃V2,T2.  L ⊢ V1 ➡* V2 & L ⊢ T1 ➡* T2 &
                                     L ⊢ U2 ➡* ⓐV2. T2
                           ) ∨
                           ∃∃V2,W,T. L ⊢ V1 ➡* V2 &
                                     L ⊢ T1 ➡* ⓛW. T & L ⊢ ⓓV2. T ⬌* U2.
#L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5/
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #HUT0
  elim (cprs_strip … HUT0 … HU2) -U #U #H #HU2
  elim (cpr_inv_appl1 … H) -H *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5/
  | #V2 #W2 #T #T2 #HV02 #HT2 #H1 #H2 destruct
    lapply (cprs_strap1 … HV10 HV02) -V0 #HV12
    lapply (cprs_div ? (ⓓV2.T) ? ? ? HU2) -HU2 /2 width=1/ /3 width=6/
  | #V #V2 #W0 #W2 #T #T2 #HV0 #HW02 #HT2 #HV2 #H1 #H2 destruct
    lapply (cprs_strap1 … HV10 HV0) -V0 #HV1
    lapply (cprs_trans … HT10 (ⓓW2.T2) ?) -HT10 /2 width=1/ -W0 -T #HT1
    elim (sfr_delift (L.ⓓW2) (ⓐV2.T2) 0 1 ? ?) // #X #H1
    lapply (cprs_zeta_delift … H1) #H2
    lapply (cprs_trans … HU2 … H2) -HU2 -H2 #HU2T3
    elim (delift_inv_flat1 … H1) -H1 #V3 #T3 #HV23 #HT23 #H destruct
    lapply (delift_inv_lift1_eq … HV23 … HV2) -V2 [ /2 width=1/ | skip ] #H destruct
    lapply (cprs_zeta_delift … HT23) -HT23 #H
    lapply (cprs_trans … HT1 … H) -W2 -T2 /3 width=5/
  ]
| /4 width=8/
]
qed-.

lemma cprs_inv_appl_abst: ∀L,V,T,W,U. L ⊢ ⓐV.T ➡* ⓛW.U →
                          ∃∃W0,T0,V1,T1. L ⊢ T ➡* ⓛW0.T0 &
                                         L ⊢ ⓓV.T0 ➡* ⓛV1.T1 &
                                         L ⊢ ⓛW.U ➡* ⓛV1.T1.
#L #V #T #W #U #H
elim (cprs_inv_appl1_cpcs … H) -H *
[ #V0 #T0 #HV0 #HT0 #H
  elim (cprs_inv_abst1 Abst W … H) -H #W0 #U0 #_ #_ #H destruct
| #V0 #W0 #T0 #HV0 #HT0 #H
  elim (cpcs_inv_abst2 … H) -H #V1 #T1 #H1 #H2
  lapply (cprs_trans … (ⓓV.T0) … H1) -H1 /2 width=1/ -V0 /2 width=7/
]
qed-.

(* Properties on inverse basic term relocation ******************************)

lemma cpcs_zeta_delift_comm: ∀L,V,T1,T2. L.ⓓV ⊢ ▼*[O, 1] T1 ≡ T2 →
                             L ⊢ T2 ⬌* ⓓV.T1.
/3 width=1/ qed.

(* Basic_1: was only: pc3_gen_cabbr *)
lemma thin_cpcs_delift_mono: ∀L,U1,U2. L ⊢ U1 ⬌* U2 →
                             ∀K,d,e. ▼*[d, e] L ≡ K → ∀T1. L ⊢ ▼*[d, e] U1 ≡ T1 →
                             ∀T2. L ⊢ ▼*[d, e] U2 ≡ T2 → K ⊢ T1 ⬌* T2.
#L #U1 #U2 #H #K #d #e #HLK #T1 #HTU1 #T2 #HTU2
elim (cpcs_inv_cprs … H) -H #U #HU1 #HU2
elim (thin_cprs_delift_conf … HU1 … HLK … HTU1) -U1 #T #HT1 #HUT
elim (thin_cprs_delift_conf … HU2 … HLK … HTU2) -U2 -HLK #X #HT2 #H
lapply (delift_mono … H … HUT) -L #H destruct /2 width=3/
qed.
