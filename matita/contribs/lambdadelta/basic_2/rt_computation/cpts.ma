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

include "ground_2/lib/ltc.ma".
include "basic_2/notation/relations/ptystar_6.ma".
include "basic_2/rt_transition/cpt.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-COMPUTATION FOR TERMS ***************)

definition cpts (h) (G) (L): relation3 nat term term ≝
           ltc … plus … (cpt h G L).

interpretation
  "t-bound context-sensitive parallel t-computarion (term)"
  'PTyStar h n G L T1 T2 = (cpts h G L n T1 T2).

(* Basic eliminators ********************************************************)

lemma cpts_ind_sn (h) (G) (L) (T2) (Q:relation2 …):
                  Q 0 T2 →
                  (∀n1,n2,T1,T. ❪G,L❫ ⊢ T1 ⬆[h,n1] T → ❪G,L❫ ⊢ T ⬆*[h,n2] T2 → Q n2 T → Q (n1+n2) T1) →
                  ∀n,T1. ❪G,L❫ ⊢ T1 ⬆*[h,n] T2 → Q n T1.
#h #G #L #T2 #Q @ltc_ind_sn_refl //
qed-.

lemma cpts_ind_dx (h) (G) (L) (T1) (Q:relation2 …):
                  Q 0 T1 →
                  (∀n1,n2,T,T2. ❪G,L❫ ⊢ T1 ⬆*[h,n1] T → Q n1 T → ❪G,L❫ ⊢ T ⬆[h,n2] T2 → Q (n1+n2) T2) →
                  ∀n,T2. ❪G,L❫ ⊢ T1 ⬆*[h,n] T2 → Q n T2.
#h #G #L #T1 #Q @ltc_ind_dx_refl //
qed-.

(* Basic properties *********************************************************)

lemma cpt_cpts (h) (G) (L):
      ∀n,T1,T2. ❪G,L❫ ⊢ T1 ⬆[h,n] T2 → ❪G,L❫ ⊢ T1 ⬆*[h,n] T2.
/2 width=1 by ltc_rc/ qed.

lemma cpts_step_sn (h) (G) (L):
      ∀n1,T1,T. ❪G,L❫ ⊢ T1 ⬆[h,n1] T →
      ∀n2,T2. ❪G,L❫ ⊢ T ⬆*[h,n2] T2 → ❪G,L❫ ⊢ T1 ⬆*[h,n1+n2] T2.
/2 width=3 by ltc_sn/ qed-.

lemma cpts_step_dx (h) (G) (L):
      ∀n1,T1,T. ❪G,L❫ ⊢ T1 ⬆*[h,n1] T →
      ∀n2,T2. ❪G,L❫ ⊢ T ⬆[h,n2] T2 → ❪G,L❫ ⊢ T1 ⬆*[h,n1+n2] T2.
/2 width=3 by ltc_dx/ qed-.

lemma cpts_bind_dx (h) (n) (G) (L):
      ∀V1,V2. ❪G,L❫ ⊢ V1 ⬆[h,0] V2 →
      ∀I,T1,T2. ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬆*[h,n] T2 →
      ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬆*[h,n] ⓑ[p,I]V2.T2.
#h #n #G #L #V1 #V2 #HV12 #I #T1 #T2 #H #a @(cpts_ind_sn … H) -T1
/3 width=3 by cpts_step_sn, cpt_cpts, cpt_bind/ qed.

lemma cpts_appl_dx (h) (n) (G) (L):
      ∀V1,V2. ❪G,L❫ ⊢ V1 ⬆[h,0] V2 →
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆*[h,n] T2 → ❪G,L❫ ⊢ ⓐV1.T1 ⬆*[h,n] ⓐV2.T2.
#h #n #G #L #V1 #V2 #HV12 #T1 #T2 #H @(cpts_ind_sn … H) -T1
/3 width=3 by cpts_step_sn, cpt_cpts, cpt_appl/
qed.

lemma cpts_ee (h) (n) (G) (L):
      ∀U1,U2. ❪G,L❫ ⊢ U1 ⬆*[h,n] U2 →
      ∀T. ❪G,L❫ ⊢ ⓝU1.T ⬆*[h,↑n] U2.
#h #n #G #L #U1 #U2 #H @(cpts_ind_sn … H) -U1 -n
[ /3 width=1 by cpt_cpts, cpt_ee/
| #n1 #n2 #U1 #U #HU1 #HU2 #_ #T >plus_S1
  /3 width=3 by cpts_step_sn, cpt_ee/
]
qed.

lemma cpts_refl (h) (G) (L): reflexive … (cpts h G L 0).
/2 width=1 by cpt_cpts/ qed.

(* Advanced properties ******************************************************)

lemma cpts_sort (h) (G) (L) (n):
      ∀s. ❪G,L❫ ⊢ ⋆s ⬆*[h,n] ⋆((next h)^n s).
#h #G #L #n elim n -n [ // ]
#n #IH #s <plus_SO_dx
/3 width=3 by cpts_step_dx, cpt_sort/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpts_inv_sort_sn (h) (n) (G) (L) (s):
      ∀X2. ❪G,L❫ ⊢ ⋆s ⬆*[h,n] X2 → X2 = ⋆(((next h)^n) s).
#h #n #G #L #s #X2 #H @(cpts_ind_dx … H) -X2 //
#n1 #n2 #X #X2 #_ #IH #HX2 destruct
elim (cpt_inv_sort_sn … HX2) -HX2 #H #_ destruct //
qed-.

lemma cpts_inv_lref_sn_ctop (h) (n) (G) (i):
      ∀X2. ❪G,⋆❫ ⊢ #i ⬆*[h,n] X2 → ∧∧ X2 = #i & n = 0.
#h #n #G #i #X2 #H @(cpts_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpt_inv_lref_sn_ctop … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpts_inv_zero_sn_unit (h) (n) (I) (K) (G):
      ∀X2. ❪G,K.ⓤ[I]❫ ⊢ #0 ⬆*[h,n] X2 → ∧∧ X2 = #0 & n = 0.
#h #n #I #G #K #X2 #H @(cpts_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpt_inv_zero_sn_unit … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpts_inv_gref_sn (h) (n) (G) (L) (l):
      ∀X2. ❪G,L❫ ⊢ §l ⬆*[h,n] X2 → ∧∧ X2 = §l & n = 0.
#h #n #G #L #l #X2 #H @(cpts_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpt_inv_gref_sn … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpts_inv_cast_sn (h) (n) (G) (L) (U1) (T1):
      ∀X2. ❪G,L❫ ⊢ ⓝU1.T1 ⬆*[h,n] X2 →
      ∨∨ ∃∃U2,T2. ❪G,L❫ ⊢ U1 ⬆*[h,n] U2 & ❪G,L❫ ⊢ T1 ⬆*[h,n] T2 & X2 = ⓝU2.T2
       | ∃∃m. ❪G,L❫ ⊢ U1 ⬆*[h,m] X2 & n = ↑m.
#h #n #G #L #U1 #T1 #X2 #H @(cpts_ind_dx … H) -n -X2
[ /3 width=5 by or_introl, ex3_2_intro/
| #n1 #n2 #X #X2 #_ * *
  [ #U #T #HU1 #HT1 #H #HX2 destruct
    elim (cpt_inv_cast_sn … HX2) -HX2 *
    [ #U2 #T2 #HU2 #HT2 #H destruct
      /4 width=5 by cpts_step_dx, ex3_2_intro, or_introl/
    | #m #HX2 #H destruct <plus_n_Sm
      /4 width=3 by cpts_step_dx, ex2_intro, or_intror/
    ]
  | #m #HX #H #HX2 destruct
    /4 width=3 by cpts_step_dx, ex2_intro, or_intror/
  ]
]
qed-.
