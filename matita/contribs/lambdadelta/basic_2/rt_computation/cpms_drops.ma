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

include "basic_2/relocation/drops_ltc.ma".
include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_computation/cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Advanced properties ******************************************************)

(* Note: apparently this was missing in basic_1 *)
(* Basic_2A1: uses: cprs_delta *)
lemma cpms_delta_drops (n) (h) (G):
                       ∀L,K,V,i. ⬇*[i] L ≘ K.ⓓV →
                       ∀V2. ⦃G, K⦄ ⊢ V ➡*[n, h] V2 →
                       ∀W2. ⬆*[↑i] V2 ≘ W2 → ⦃G, L⦄ ⊢ #i ➡*[n, h] W2.
#n #h #G #L #K #V #i #HLK #V2 #H @(cpms_ind_dx … H) -V2
[ /3 width=6 by cpm_cpms, cpm_delta_drops/
| #n1 #n2 #V1 #V2 #_ #IH #HV12 #W2 #HVW2
  lapply (drops_isuni_fwd_drop2 … HLK) -HLK // #HLK
  elim (lifts_total V1 (𝐔❴↑i❵)) #W1 #HVW1
  /3 width=11 by cpm_lifts_bi, cpms_step_dx/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpms_inv_lref1_drops (n) (h) (G):
                           ∀L,T2,i. ⦃G, L⦄ ⊢ #i ➡*[n, h] T2 →
                           ∨∨ ∧∧ T2 = #i & n = 0
                            | ∃∃K,V,V2. ⬇*[i] L ≘ K.ⓓV & ⦃G, K⦄ ⊢ V ➡*[n, h] V2 &
                                        ⬆*[↑i] V2 ≘ T2
                            | ∃∃m,K,V,V2. ⬇*[i] L ≘ K.ⓛV & ⦃G, K⦄ ⊢ V ➡*[m, h] V2 &
                                          ⬆*[↑i] V2 ≘ T2 & n = ↑m.
#n #h #G #L #T2 #i #H @(cpms_ind_dx … H) -T2
[ /3 width=1 by or3_intro0, conj/
| #n1 #n2 #T #T2 #_ #IH #HT2 cases IH -IH *
  [ #H1 #H2 destruct
    elim (cpm_inv_lref1_drops … HT2) -HT2 *
    [ /3 width=1 by or3_intro0, conj/
    | /4 width=6 by cpm_cpms, or3_intro1, ex3_3_intro/
    | /4 width=8 by cpm_cpms, or3_intro2, ex4_4_intro/
    ]
  | #K #V0 #V #HLK #HV0 #HVT
    lapply (drops_isuni_fwd_drop2 … HLK) // #H0LK
    elim (cpm_inv_lifts_sn … HT2 … H0LK … HVT) -H0LK -T
    /4 width=6 by cpms_step_dx, ex3_3_intro, or3_intro1/
  | #m #K #V0 #V #HLK #HV0 #HVT #H destruct
    lapply (drops_isuni_fwd_drop2 … HLK) // #H0LK
    elim (cpm_inv_lifts_sn … HT2 … H0LK … HVT) -H0LK -T
    /4 width=8 by cpms_step_dx, ex4_4_intro, or3_intro2/
  ]
]
qed-.

(* Properties with generic slicing for local environments *******************)

lemma cpms_lifts_sn: ∀n,h,G. d_liftable2_sn … lifts (λL. cpms h G L n).
/3 width=6 by d2_liftable_sn_ltc, cpm_lifts_sn/ qed-.

(* Basic_2A1: uses: scpds_lift *)
(* Basic_2A1: includes: cprs_lift *)
(* Basic_1: includes: pr3_lift *)
lemma cpms_lifts_bi: ∀n,h,G. d_liftable2_bi … lifts (λL. cpms h G L n).
#n #h #G @d_liftable2_sn_bi
/2 width=6 by cpms_lifts_sn, lifts_mono/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: uses: scpds_inv_lift1 *)
(* Basic_2A1: includes: cprs_inv_lift1 *)
(* Basic_1: includes: pr3_gen_lift *)
lemma cpms_inv_lifts_sn: ∀n,h,G. d_deliftable2_sn … lifts (λL. cpms h G L n).
/3 width=6 by d2_deliftable_sn_ltc, cpm_inv_lifts_sn/ qed-.

lemma cpms_inv_lifts_bi: ∀n,h,G. d_deliftable2_bi … lifts (λL. cpms h G L n).
#n #h #G @d_deliftable2_sn_bi
/2 width=6 by cpms_inv_lifts_sn, lifts_inj/
qed-.
