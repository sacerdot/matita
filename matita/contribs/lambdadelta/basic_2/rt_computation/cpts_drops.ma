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
include "basic_2/rt_transition/cpt_drops.ma".
include "basic_2/rt_computation/cpts.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-COMPUTATION FOR TERMS ***************)

(* Properties with generic slicing for local environments *******************)

lemma cpts_lifts_sn (h) (n) (G):
      d_liftable2_sn … lifts (λL. cpts h G L n).
/3 width=6 by d2_liftable_sn_ltc, cpt_lifts_sn/ qed-.

lemma cpts_lifts_bi (h) (n) (G):
      d_liftable2_bi … lifts (λL. cpts h G L n).
#h #n #G @d_liftable2_sn_bi
/2 width=6 by cpts_lifts_sn, lifts_mono/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma cpts_inv_lifts_sn (h) (n) (G):
      d_deliftable2_sn … lifts (λL. cpts h G L n).
/3 width=6 by d2_deliftable_sn_ltc, cpt_inv_lifts_sn/ qed-.

lemma cpts_inv_lifts_bi (h) (n) (G):
      d_deliftable2_bi … lifts (λL. cpts h G L n).
#h #n #G @d_deliftable2_sn_bi
/2 width=6 by cpts_inv_lifts_sn, lifts_inj/
qed-.

(* Advanced properties ******************************************************)

lemma cpts_delta (h) (n) (G):
      ∀K,V1,V2. ❪G,K❫ ⊢ V1 ⬆*[h,n] V2 →
      ∀W2. ⇧*[1] V2 ≘ W2 → ❪G,K.ⓓV1❫ ⊢ #0 ⬆*[h,n] W2.
#h #n #G #K #V1 #V2 #H @(cpts_ind_dx … H) -V2
[ /3 width=3 by cpt_cpts, cpt_delta/
| #n1 #n2 #V #V2 #_ #IH #HV2 #W2 #HVW2
  elim (lifts_total V (𝐔❨1❩)) #W #HVW
  /5 width=11 by cpts_step_dx, cpt_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpts_ell (h) (n) (G):
      ∀K,V1,V2. ❪G,K❫ ⊢ V1 ⬆*[h,n] V2 →
      ∀W2. ⇧*[1] V2 ≘ W2 → ❪G,K.ⓛV1❫ ⊢ #0 ⬆*[h,↑n] W2.
#h #n #G #K #V1 #V2 #H @(cpts_ind_dx … H) -V2
[ /3 width=3 by cpt_cpts, cpt_ell/
| #n1 #n2 #V #V2 #_ #IH #HV2 #W2 #HVW2
  elim (lifts_total V (𝐔❨1❩)) #W #HVW >plus_S1
  /5 width=11 by cpts_step_dx, cpt_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpts_lref (h) (n) (I) (G):
      ∀K,T,i. ❪G,K❫ ⊢ #i ⬆*[h,n] T →
      ∀U. ⇧*[1] T ≘ U → ❪G,K.ⓘ[I]❫ ⊢ #↑i ⬆*[h,n] U.
#h #n #I #G #K #T #i #H @(cpts_ind_dx … H) -T
[ /3 width=3 by cpt_cpts, cpt_lref/
| #n1 #n2 #T #T2 #_ #IH #HT2 #U2 #HTU2
  elim (lifts_total T (𝐔❨1❩)) #U #TU
  /5 width=11 by cpts_step_dx, cpt_lifts_bi, drops_refl, drops_drop/
]
qed.

lemma cpts_cast_sn (h) (n) (G) (L):
      ∀U1,U2. ❪G,L❫ ⊢ U1 ⬆*[h,n] U2 →
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆[h,n] T2 → ❪G,L❫ ⊢ ⓝU1.T1 ⬆*[h,n] ⓝU2.T2.
#h #n #G #L #U1 #U2 #H @(cpts_ind_sn … H) -U1 -n
[ /3 width=3 by cpt_cpts, cpt_cast/
| #n1 #n2 #U1 #U #HU1 #_ #IH #T1 #T2 #H
  elim (cpt_fwd_plus … H) -H #T #HT1 #HT2
  /3 width=3 by cpts_step_sn, cpt_cast/
]
qed.

lemma cpts_delta_drops (h) (n) (G):
      ∀L,K,V,i. ⇩*[i] L ≘ K.ⓓV →
      ∀V2. ❪G,K❫ ⊢ V ⬆*[h,n] V2 →
      ∀W2. ⇧*[↑i] V2 ≘ W2 → ❪G,L❫ ⊢ #i ⬆*[h,n] W2.
#h #n #G #L #K #V #i #HLK #V2 #H @(cpts_ind_dx … H) -V2
[ /3 width=6 by cpt_cpts, cpt_delta_drops/
| #n1 #n2 #V1 #V2 #_ #IH #HV12 #W2 #HVW2
  lapply (drops_isuni_fwd_drop2 … HLK) -HLK // #HLK
  elim (lifts_total V1 (𝐔❨↑i❩)) #W1 #HVW1
  /3 width=11 by cpt_lifts_bi, cpts_step_dx/
]
qed.

lemma cpts_ell_drops (h) (n) (G):
      ∀L,K,W,i. ⇩*[i] L ≘ K.ⓛW →
      ∀W2. ❪G,K❫ ⊢ W ⬆*[h,n] W2 →
      ∀V2. ⇧*[↑i] W2 ≘ V2 → ❪G,L❫ ⊢ #i ⬆*[h,↑n] V2.
#h #n #G #L #K #W #i #HLK #W2 #H @(cpts_ind_dx … H) -W2
[ /3 width=6 by cpt_cpts, cpt_ell_drops/
| #n1 #n2 #W1 #W2 #_ #IH #HW12 #V2 #HWV2
  lapply (drops_isuni_fwd_drop2 … HLK) -HLK // #HLK
  elim (lifts_total W1 (𝐔❨↑i❩)) #V1 #HWV1 >plus_S1
  /3 width=11 by cpt_lifts_bi, cpts_step_dx/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpts_inv_lref_sn_drops (h) (n) (G) (L) (i):
      ∀X2. ❪G,L❫ ⊢ #i ⬆*[h,n] X2 →
      ∨∨ ∧∧ X2 = #i & n = 0
       | ∃∃K,V,V2. ⇩*[i] L ≘ K.ⓓV & ❪G,K❫ ⊢ V ⬆*[h,n] V2 & ⇧*[↑i] V2 ≘ X2
       | ∃∃m,K,V,V2. ⇩*[i] L ≘ K.ⓛV & ❪G,K❫ ⊢ V ⬆*[h,m] V2 & ⇧*[↑i] V2 ≘ X2 & n = ↑m.
#h #n #G #L #i #X2 #H @(cpts_ind_dx … H) -X2
[ /3 width=1 by or3_intro0, conj/
| #n1 #n2 #T #T2 #_ #IH #HT2 cases IH -IH *
  [ #H1 #H2 destruct
    elim (cpt_inv_lref_sn_drops … HT2) -HT2 *
    [ /3 width=1 by or3_intro0, conj/
    | /4 width=6 by cpt_cpts, or3_intro1, ex3_3_intro/
    | /4 width=8 by cpt_cpts, or3_intro2, ex4_4_intro/
    ]
  | #K #V0 #V #HLK #HV0 #HVT
    lapply (drops_isuni_fwd_drop2 … HLK) // #H0LK
    elim (cpt_inv_lifts_sn … HT2 … H0LK … HVT) -H0LK -T
    /4 width=6 by cpts_step_dx, ex3_3_intro, or3_intro1/
  | #m #K #V0 #V #HLK #HV0 #HVT #H destruct
    lapply (drops_isuni_fwd_drop2 … HLK) // #H0LK
    elim (cpt_inv_lifts_sn … HT2 … H0LK … HVT) -H0LK -T
    /4 width=8 by cpts_step_dx, ex4_4_intro, or3_intro2/
  ]
]
qed-.

lemma cpts_inv_delta_sn (h) (n) (G) (K) (V):
      ∀X2. ❪G,K.ⓓV❫ ⊢ #0 ⬆*[h,n] X2 →
      ∨∨ ∧∧ X2 = #0 & n = 0
       | ∃∃V2. ❪G,K❫ ⊢ V ⬆*[h,n] V2 & ⇧*[1] V2 ≘ X2.
#h #n #G #K #V #X2 #H
elim (cpts_inv_lref_sn_drops … H) -H *
[ /3 width=1 by or_introl, conj/
| #Y #X #V2 #H #HV2 #HVT2
  lapply (drops_fwd_isid … H ?) -H [ // ] #H destruct
  /3 width=3 by ex2_intro, or_intror/
| #m #Y #X #V2 #H #HV2 #HVT2
  lapply (drops_fwd_isid … H ?) -H [ // ] #H destruct
]
qed-.

lemma cpts_inv_ell_sn (h) (n) (G) (K) (V):
      ∀X2. ❪G,K.ⓛV❫ ⊢ #0 ⬆*[h,n] X2 →
      ∨∨ ∧∧ X2 = #0 & n = 0
       | ∃∃m,V2. ❪G,K❫ ⊢ V ⬆*[h,m] V2 & ⇧*[1] V2 ≘ X2 & n = ↑m.
#h #n #G #K #V #X2 #H
elim (cpts_inv_lref_sn_drops … H) -H *
[ /3 width=1 by or_introl, conj/
| #Y #X #V2 #H #HV2 #HVT2
  lapply (drops_fwd_isid … H ?) -H [ // ] #H destruct
| #m #Y #X #V2 #H #HV2 #HVT2 #H0 destruct
  lapply (drops_fwd_isid … H ?) -H [ // ] #H destruct
  /3 width=5 by ex3_2_intro, or_intror/
]
qed-.

lemma cpts_inv_lref_sn (h) (n) (I) (G) (K) (i):
      ∀X2. ❪G,K.ⓘ[I]❫ ⊢ #↑i ⬆*[h,n] X2 →
      ∨∨ ∧∧ X2 = #↑i & n = 0
       | ∃∃T2. ❪G,K❫ ⊢ #i ⬆*[h,n] T2 & ⇧*[1] T2 ≘ X2.
#h #n #I #G #K #i #X2 #H
elim (cpts_inv_lref_sn_drops … H) -H *
[ /3 width=1 by or_introl, conj/
| #L #V #V2 #H #HV2 #HVU2
  lapply (drops_inv_drop1 … H) -H #HLK
  elim (lifts_split_trans … HVU2 (𝐔❨↑i❩) (𝐔❨1❩)) -HVU2
  [| // ] #T2 #HVT2 #HTU2
  /4 width=6 by cpts_delta_drops, ex2_intro, or_intror/
| #m #L #V #V2 #H #HV2 #HVU2 #H0 destruct
  lapply (drops_inv_drop1 … H) -H #HLK
  elim (lifts_split_trans … HVU2 (𝐔❨↑i❩) (𝐔❨1❩)) -HVU2
  [| // ] #T2 #HVT2 #HTU2
  /4 width=6 by cpts_ell_drops, ex2_intro, or_intror/
]
qed-.

lemma cpts_inv_succ_sn (h) (n) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆*[h,↑n] T2 →
      ∃∃T. ❪G,L❫ ⊢ T1 ⬆*[h,1] T & ❪G,L❫ ⊢ T ⬆*[h,n] T2.
#h #n #G #L #T1 #T2
@(insert_eq_0 … (↑n)) #m #H
@(cpts_ind_sn … H) -T1 -m
[ #H destruct
| #x1 #n2 #T1 #T #HT1 #HT2 #IH #H
  elim (plus_inv_S3_sn x1 n2) [1,2: * |*: // ] -H
  [ #H1 #H2 destruct -HT2
    elim IH -IH // #T0 #HT0 #HT02
    /3 width=3 by cpts_step_sn, ex2_intro/
  | #n1 #H1 #H2 destruct -IH
    elim (cpt_fwd_plus … 1 n1 … T1 T) [|*: // ] -HT1 #T0 #HT10 #HT0
    /3 width=5 by cpts_step_sn, cpt_cpts, ex2_intro/
  ]
]
qed-.
