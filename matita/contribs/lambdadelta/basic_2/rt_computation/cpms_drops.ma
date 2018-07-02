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

include "static_2/relocation/drops_ltc.ma".
include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_computation/cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

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

(* Advanced properties ******************************************************)

lemma cpms_delta (n) (h) (G): ∀K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡*[n, h] V2 →
                              ∀W2. ⬆*[1] V2 ≘ W2 → ⦃G, K.ⓓV1⦄ ⊢ #0 ➡*[n, h] W2.
#n #h #G #K #V1 #V2 #H @(cpms_ind_dx … H) -V2
[ /3 width=3 by cpm_cpms, cpm_delta/
| #n1 #n2 #V #V2 #_ #IH #HV2 #W2 #HVW2
  elim (lifts_total V (𝐔❴1❵)) #W #HVW
  /5 width=11 by cpms_step_dx, cpm_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpms_ell (n) (h) (G): ∀K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡*[n, h] V2 →
                            ∀W2. ⬆*[1] V2 ≘ W2 → ⦃G, K.ⓛV1⦄ ⊢ #0 ➡*[↑n, h] W2.
#n #h #G #K #V1 #V2 #H @(cpms_ind_dx … H) -V2
[ /3 width=3 by cpm_cpms, cpm_ell/
| #n1 #n2 #V #V2 #_ #IH #HV2 #W2 #HVW2
  elim (lifts_total V (𝐔❴1❵)) #W #HVW >plus_S1
  /5 width=11 by cpms_step_dx, cpm_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpms_lref (n) (h) (I) (G): ∀K,T,i. ⦃G, K⦄ ⊢ #i ➡*[n, h] T →
                                 ∀U. ⬆*[1] T ≘ U → ⦃G, K.ⓘ{I}⦄ ⊢ #↑i ➡*[n, h] U.
#n #h #I #G #K #T #i #H @(cpms_ind_dx … H) -T
[ /3 width=3 by cpm_cpms, cpm_lref/
| #n1 #n2 #T #T2 #_ #IH #HT2 #U2 #HTU2
  elim (lifts_total T (𝐔❴1❵)) #U #TU
  /5 width=11 by cpms_step_dx, cpm_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpms_cast_sn (n) (h) (G) (L):
                   ∀U1,U2. ⦃G, L⦄ ⊢ U1 ➡*[n, h] U2 →
                   ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡[n, h] T2 →
                   ⦃G, L⦄ ⊢ ⓝU1.T1 ➡*[n, h] ⓝU2.T2.
#n #h #G #L #U1 #U2 #H @(cpms_ind_sn … H) -U1 -n
[ /3 width=3 by cpm_cpms, cpm_cast/
| #n1 #n2 #U1 #U #HU1 #_ #IH #T1 #T2 #H
  elim (cpm_fwd_plus … H) -H #T #HT1 #HT2
  /3 width=3 by cpms_step_sn, cpm_cast/
]
qed.

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

fact cpms_inv_succ_sn (n) (h) (G) (L):
                      ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[↑n, h] T2 →
                      ∃∃T. ⦃G, L⦄ ⊢ T1 ➡*[1, h] T & ⦃G, L⦄ ⊢ T ➡*[n, h] T2.
#n #h #G #L #T1 #T2
@(insert_eq_0 … (↑n)) #m #H
@(cpms_ind_sn … H) -T1 -m
[ #H destruct
| #x1 #n2 #T1 #T #HT1 #HT2 #IH #H
  elim (plus_inv_S3_sn x1 n2) [1,2: * |*: // ] -H
  [ #H1 #H2 destruct -HT2
    elim IH -IH // #T0 #HT0 #HT02
    /3 width=3 by cpms_step_sn, ex2_intro/
  | #n1 #H1 #H2 destruct -IH
    elim (cpm_fwd_plus … 1 n1 T1 T) [|*: // ] -HT1 #T0 #HT10 #HT0
    /3 width=5 by cpms_step_sn, cpm_cpms, ex2_intro/
  ]
]
qed-.
