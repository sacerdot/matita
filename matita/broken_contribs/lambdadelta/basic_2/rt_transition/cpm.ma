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

include "ground/xoa/ex_4_1.ma".
include "ground/xoa/ex_4_3.ma".
include "ground/xoa/ex_5_6.ma".
include "ground/xoa/ex_6_7.ma".
include "ground/counters/rtc_max_shift.ma".
include "ground/counters/rtc_isrt_plus.ma".
include "ground/counters/rtc_isrt_max_shift.ma".
include "static_2/syntax/sh.ma".
include "basic_2/notation/relations/pred_6.ma".
include "basic_2/rt_transition/cpg.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Basic_2A1: includes: cpr *)
definition cpm (h) (G) (L) (n): relation2 term term ≝
           λT1,T2. ∃∃c. 𝐑𝐓❨n,c❩ & ❨G,L❩ ⊢ T1 ⬈[sh_is_next h,rtc_eq_t,c] T2.

interpretation
  "t-bound context-sensitive parallel rt-transition (term)"
  'PRed h n G L T1 T2 = (cpm h G L n T1 T2).

(* Basic properties *********************************************************)

lemma cpm_ess (h) (G) (L):
      ∀s. ❨G,L❩ ⊢ ⋆s ➡[h,1] ⋆(⫯[h]s).
/3 width=3 by cpg_ess, ex2_intro/ qed.

lemma cpm_delta (h) (n) (G) (K):
      ∀V1,V2,W2. ❨G,K❩ ⊢ V1 ➡[h,n] V2 →
      ⇧[1] V2 ≘ W2 → ❨G,K.ⓓV1❩ ⊢ #0 ➡[h,n] W2.
#h #n #G #K #V1 #V2 #W2 *
/3 width=5 by cpg_delta, ex2_intro/
qed.

lemma cpm_ell (h) (n) (G) (K):
      ∀V1,V2,W2. ❨G,K❩ ⊢ V1 ➡[h,n] V2 →
      ⇧[1] V2 ≘ W2 → ❨G,K.ⓛV1❩ ⊢ #0 ➡[h,↑n] W2.
#h #n #G #K #V1 #V2 #W2 *
/3 width=5 by cpg_ell, ex2_intro, isrt_succ/
qed.

lemma cpm_lref (h) (n) (G) (K):
      ∀I,T,U,i. ❨G,K❩ ⊢ #i ➡[h,n] T →
      ⇧[1] T ≘ U → ❨G,K.ⓘ[I]❩ ⊢ #↑i ➡[h,n] U.
#h #n #G #K #I #T #U #i *
/3 width=5 by cpg_lref, ex2_intro/
qed.

(* Basic_2A1: includes: cpr_bind *)
lemma cpm_bind (h) (n) (G) (L):
      ∀p,I,V1,V2,T1,T2.
      ❨G,L❩ ⊢ V1 ➡[h,0] V2 → ❨G,L.ⓑ[I]V1❩ ⊢ T1 ➡[h,n] T2 →
      ❨G,L❩ ⊢ ⓑ[p,I]V1.T1 ➡[h,n] ⓑ[p,I]V2.T2.
#h #n #G #L #p #I #V1 #V2 #T1 #T2 * #cV #HcV #HV12 *
/5 width=5 by cpg_bind, isrt_max_O1, isr_shift, ex2_intro/
qed.

lemma cpm_appl (h) (n) (G) (L):
      ∀V1,V2,T1,T2.
      ❨G,L❩ ⊢ V1 ➡[h,0] V2 → ❨G,L❩ ⊢ T1 ➡[h,n] T2 →
      ❨G,L❩ ⊢ ⓐV1.T1 ➡[h,n] ⓐV2.T2.
#h #n #G #L #V1 #V2 #T1 #T2 * #cV #HcV #HV12 *
/5 width=5 by isrt_max_O1, isr_shift, cpg_appl, ex2_intro/
qed.

lemma cpm_cast (h) (n) (G) (L):
      ∀U1,U2,T1,T2.
      ❨G,L❩ ⊢ U1 ➡[h,n] U2 → ❨G,L❩ ⊢ T1 ➡[h,n] T2 →
      ❨G,L❩ ⊢ ⓝU1.T1 ➡[h,n] ⓝU2.T2.
#h #n #G #L #U1 #U2 #T1 #T2 * #cU #HcU #HU12 *
/4 width=6 by cpg_cast, isrt_max_idem1, isrt_mono, ex2_intro/
qed.

(* Basic_2A1: includes: cpr_zeta *)
lemma cpm_zeta (h) (n) (G) (L):
      ∀T1,T. ⇧[1] T ≘ T1 → ∀T2. ❨G,L❩ ⊢ T ➡[h,n] T2 →
      ∀V. ❨G,L❩ ⊢ +ⓓV.T1 ➡[h,n] T2.
#h #n #G #L #T1 #T #HT1 #T2 *
/3 width=5 by cpg_zeta, isrt_plus_O2, ex2_intro/
qed.

(* Basic_2A1: includes: cpr_eps *)
lemma cpm_eps (h) (n) (G) (L):
      ∀V,T1,T2. ❨G,L❩ ⊢ T1 ➡[h,n] T2 → ❨G,L❩ ⊢ ⓝV.T1 ➡[h,n] T2.
#h #n #G #L #V #T1 #T2 *
/3 width=3 by cpg_eps, isrt_plus_O2, ex2_intro/
qed.

lemma cpm_ee (h) (n) (G) (L):
      ∀V1,V2,T. ❨G,L❩ ⊢ V1 ➡[h,n] V2 → ❨G,L❩ ⊢ ⓝV1.T ➡[h,↑n] V2.
#h #n #G #L #V1 #V2 #T *
/3 width=3 by cpg_ee, isrt_succ, ex2_intro/
qed.

(* Basic_2A1: includes: cpr_beta *)
lemma cpm_beta (h) (n) (G) (L):
      ∀p,V1,V2,W1,W2,T1,T2.
      ❨G,L❩ ⊢ V1 ➡[h,0] V2 → ❨G,L❩ ⊢ W1 ➡[h,0] W2 → ❨G,L.ⓛW1❩ ⊢ T1 ➡[h,n] T2 →
      ❨G,L❩ ⊢ ⓐV1.ⓛ[p]W1.T1 ➡[h,n] ⓓ[p]ⓝW2.V2.T2.
#h #n #G #L #p #V1 #V2 #W1 #W2 #T1 #T2 * #riV #rhV #HV12 * #riW #rhW #HW12 *
/6 width=7 by cpg_beta, isrt_plus_O2, isrt_max, isr_shift, ex2_intro/
qed.

(* Basic_2A1: includes: cpr_theta *)
lemma cpm_theta (h) (n) (G) (L):
      ∀p,V1,V,V2,W1,W2,T1,T2.
      ❨G,L❩ ⊢ V1 ➡[h,0] V → ⇧[1] V ≘ V2 → ❨G,L❩ ⊢ W1 ➡[h,0] W2 →
      ❨G,L.ⓓW1❩ ⊢ T1 ➡[h,n] T2 → ❨G,L❩ ⊢ ⓐV1.ⓓ[p]W1.T1 ➡[h,n] ⓓ[p]W2.ⓐV2.T2.
#h #n #G #L #p #V1 #V #V2 #W1 #W2 #T1 #T2 * #riV #rhV #HV1 #HV2 * #riW #rhW #HW12 *
/6 width=9 by cpg_theta, isrt_plus_O2, isrt_max, isr_shift, ex2_intro/
qed.

(* Basic properties with r-transition ***************************************)

(* Note: this is needed by cpms_ind_sn and cpms_ind_dx *)
(* Basic_1: includes by definition: pr0_refl *)
(* Basic_2A1: includes: cpr_atom *)
lemma cpr_refl (h) (G) (L): reflexive … (cpm h G L 0).
/3 width=3 by cpg_refl, ex2_intro/ qed.

(* Advanced properties ******************************************************)

lemma cpm_sort (h) (n) (G) (L): n ≤ 1 →
      ∀s. ❨G,L❩ ⊢ ⋆s ➡[h,n] ⋆((next h)^n s).
#h * //
#n #G #L #H #s <(le_n_O_to_eq n) /2 width=1 by le_S_S_to_le/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpm_inv_atom1 (h) (n) (G) (L):
      ∀J,T2. ❨G,L❩ ⊢ ⓪[J] ➡[h,n] T2 →
      ∨∨ ∧∧ T2 = ⓪[J] & n = 0
       | ∃∃s. T2 = ⋆(⫯[h]s) & J = Sort s & n = 1
       | ∃∃K,V1,V2. ❨G,K❩ ⊢ V1 ➡[h,n] V2 & ⇧[1] V2 ≘ T2 & L = K.ⓓV1 & J = LRef 0
       | ∃∃m,K,V1,V2. ❨G,K❩ ⊢ V1 ➡[h,m] V2 & ⇧[1] V2 ≘ T2 & L = K.ⓛV1 & J = LRef 0 & n = ↑m
       | ∃∃I,K,T,i. ❨G,K❩ ⊢ #i ➡[h,n] T & ⇧[1] T ≘ T2 & L = K.ⓘ[I] & J = LRef (↑i).
#h #n #G #L #J #T2 * #c #Hc #H elim (cpg_inv_atom1 … H) -H *
[ #H1 #H2 destruct /4 width=1 by isrt_inv_00, or5_intro0, conj/
| #s1 #s2 #H1 #H2 #H3 #H4 destruct /4 width=3 by isrt_inv_01, or5_intro1, ex3_intro/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 #H3 destruct
  /4 width=6 by or5_intro2, ex4_3_intro, ex2_intro/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 #H3 destruct
  elim (isrt_inv_plus_SO_dx … Hc) -Hc // #m #Hc #H destruct
  /4 width=9 by or5_intro3, ex5_4_intro, ex2_intro/
| #I #K #V2 #i #HV2 #HVT2 #H1 #H2 destruct
  /4 width=8 by or5_intro4, ex4_4_intro, ex2_intro/
]
qed-.

lemma cpm_inv_sort1 (h) (n) (G) (L):
      ∀T2,s1. ❨G,L❩ ⊢ ⋆s1 ➡[h,n] T2 →
      ∧∧ T2 = ⋆(((next h)^n) s1) & n ≤ 1.
#h #n #G #L #T2 #s1 * #c #Hc #H
elim (cpg_inv_sort1 … H) -H *
[ #H1 #H2 destruct
  lapply (isrt_inv_00 … Hc)
| #s2 #H1 #H2 #H3 destruct
  lapply (isrt_inv_01 … Hc)
] -Hc
#H destruct /2 width=1 by conj/
qed-.

lemma cpm_inv_zero1 (h) (n) (G) (L):
      ∀T2. ❨G,L❩ ⊢ #0 ➡[h,n] T2 →
      ∨∨ ∧∧ T2 = #0 & n = 0
       | ∃∃K,V1,V2. ❨G,K❩ ⊢ V1 ➡[h,n] V2 & ⇧[1] V2 ≘ T2 & L = K.ⓓV1
       | ∃∃m,K,V1,V2. ❨G,K❩ ⊢ V1 ➡[h,m] V2 & ⇧[1] V2 ≘ T2 & L = K.ⓛV1 & n = ↑m.
#h #n #G #L #T2 * #c #Hc #H elim (cpg_inv_zero1 … H) -H *
[ #H1 #H2 destruct /4 width=1 by isrt_inv_00, or3_intro0, conj/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 destruct
  /4 width=8 by or3_intro1, ex3_3_intro, ex2_intro/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 destruct
  elim (isrt_inv_plus_SO_dx … Hc) -Hc // #m #Hc #H destruct
  /4 width=8 by or3_intro2, ex4_4_intro, ex2_intro/
]
qed-.

lemma cpm_inv_zero1_unit (h) (n) (I) (K) (G):
      ∀X2. ❨G,K.ⓤ[I]❩ ⊢ #0 ➡[h,n] X2 → ∧∧ X2 = #0 & n = 0.
#h #n #I #G #K #X2 #H
elim (cpm_inv_zero1 … H) -H *
[ #H1 #H2 destruct /2 width=1 by conj/
| #Y #X1 #X2 #_ #_ #H destruct
| #m #Y #X1 #X2 #_ #_ #H destruct
]
qed.

lemma cpm_inv_lref1 (h) (n) (G) (L):
      ∀T2,i. ❨G,L❩ ⊢ #↑i ➡[h,n] T2 →
      ∨∨ ∧∧ T2 = #(↑i) & n = 0
       | ∃∃I,K,T. ❨G,K❩ ⊢ #i ➡[h,n] T & ⇧[1] T ≘ T2 & L = K.ⓘ[I].
#h #n #G #L #T2 #i * #c #Hc #H elim (cpg_inv_lref1 … H) -H *
[ #H1 #H2 destruct /4 width=1 by isrt_inv_00, or_introl, conj/
| #I #K #V2 #HV2 #HVT2 #H destruct
 /4 width=6 by ex3_3_intro, ex2_intro, or_intror/
]
qed-.

lemma cpm_inv_lref1_ctop (h) (n) (G):
      ∀X2,i. ❨G,⋆❩ ⊢ #i ➡[h,n] X2 → ∧∧ X2 = #i & n = 0.
#h #n #G #X2 * [| #i ] #H
[ elim (cpm_inv_zero1 … H) -H *
  [ #H1 #H2 destruct /2 width=1 by conj/
  | #Y #X1 #X2 #_ #_ #H destruct
  | #m #Y #X1 #X2 #_ #_ #H destruct
  ]
| elim (cpm_inv_lref1 … H) -H *
  [ #H1 #H2 destruct /2 width=1 by conj/
  | #Z #Y #X0 #_ #_ #H destruct
  ]
]
qed.

lemma cpm_inv_gref1 (h) (n) (G) (L):
      ∀T2,l. ❨G,L❩ ⊢ §l ➡[h,n] T2 → ∧∧ T2 = §l & n = 0.
#h #n #G #L #T2 #l * #c #Hc #H elim (cpg_inv_gref1 … H) -H
#H1 #H2 destruct /3 width=1 by isrt_inv_00, conj/
qed-.

(* Basic_2A1: includes: cpr_inv_bind1 *)
lemma cpm_inv_bind1 (h) (n) (G) (L):
      ∀p,I,V1,T1,U2. ❨G,L❩ ⊢ ⓑ[p,I]V1.T1 ➡[h,n] U2 →
      ∨∨ ∃∃V2,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 & ❨G,L.ⓑ[I]V1❩ ⊢ T1 ➡[h,n] T2 & U2 = ⓑ[p,I]V2.T2
       | ∃∃T. ⇧[1] T ≘ T1 & ❨G,L❩ ⊢ T ➡[h,n] U2 & p = true & I = Abbr.
#h #n #G #L #p #I #V1 #T1 #U2 * #c #Hc #H elim (cpg_inv_bind1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct
  elim (isrt_inv_max … Hc) -Hc #nV #nT #HcV #HcT #H destruct
  elim (isrt_inv_shift … HcV) -HcV #HcV #H destruct
  /4 width=5 by ex3_2_intro, ex2_intro, or_introl/
| #cT #T2 #HT21 #HTU2 #H1 #H2 #H3 destruct
  /5 width=5 by isrt_inv_plus_O_dx, ex4_intro, ex2_intro, or_intror/
]
qed-.

(* Basic_1: includes: pr0_gen_abbr pr2_gen_abbr *)
(* Basic_2A1: includes: cpr_inv_abbr1 *)
lemma cpm_inv_abbr1 (h) (n) (G) (L):
      ∀p,V1,T1,U2. ❨G,L❩ ⊢ ⓓ[p]V1.T1 ➡[h,n] U2 →
      ∨∨ ∃∃V2,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 & ❨G,L.ⓓV1❩ ⊢ T1 ➡[h,n] T2 & U2 = ⓓ[p]V2.T2
       | ∃∃T. ⇧[1] T ≘ T1 & ❨G,L❩ ⊢ T ➡[h,n] U2 & p = true.
#h #n #G #L #p #V1 #T1 #U2 #H
elim (cpm_inv_bind1 … H) -H
[ /3 width=1 by or_introl/
| * /3 width=3 by ex3_intro, or_intror/
]
qed-.

(* Basic_1: includes: pr0_gen_abst pr2_gen_abst *)
(* Basic_2A1: includes: cpr_inv_abst1 *)
lemma cpm_inv_abst1 (h) (n) (G) (L):
      ∀p,V1,T1,U2. ❨G,L❩ ⊢ ⓛ[p]V1.T1 ➡[h,n] U2 →
      ∃∃V2,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 & ❨G,L.ⓛV1❩ ⊢ T1 ➡[h,n] T2 & U2 = ⓛ[p]V2.T2.
#h #n #G #L #p #V1 #T1 #U2 #H
elim (cpm_inv_bind1 … H) -H
[ /3 width=1 by or_introl/
| * #T #_ #_ #_ #H destruct
]
qed-.

lemma cpm_inv_abst_bi (h) (n) (G) (L):
      ∀p1,p2,V1,V2,T1,T2. ❨G,L❩ ⊢ ⓛ[p1]V1.T1 ➡[h,n] ⓛ[p2]V2.T2 →
      ∧∧ ❨G,L❩ ⊢ V1 ➡[h,0] V2 & ❨G,L.ⓛV1❩ ⊢ T1 ➡[h,n] T2 & p1 = p2.
#h #n #G #L #p1 #p2 #V1 #V2 #T1 #T2 #H
elim (cpm_inv_abst1 … H) -H #XV #XT #HV #HT #H destruct
/2 width=1 by and3_intro/
qed-.

(* Basic_1: includes: pr0_gen_appl pr2_gen_appl *)
(* Basic_2A1: includes: cpr_inv_appl1 *)
lemma cpm_inv_appl1 (h) (n) (G) (L):
      ∀V1,U1,U2. ❨G,L❩ ⊢ ⓐ V1.U1 ➡[h,n] U2 →
      ∨∨ ∃∃V2,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 & ❨G,L❩ ⊢ U1 ➡[h,n] T2 & U2 = ⓐV2.T2
       | ∃∃p,V2,W1,W2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 & ❨G,L❩ ⊢ W1 ➡[h,0] W2 & ❨G,L.ⓛW1❩ ⊢ T1 ➡[h,n] T2 & U1 = ⓛ[p]W1.T1 & U2 = ⓓ[p]ⓝW2.V2.T2
       | ∃∃p,V,V2,W1,W2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V & ⇧[1] V ≘ V2 & ❨G,L❩ ⊢ W1 ➡[h,0] W2 & ❨G,L.ⓓW1❩ ⊢ T1 ➡[h,n] T2 & U1 = ⓓ[p]W1.T1 & U2 = ⓓ[p]W2.ⓐV2.T2.
#h #n #G #L #V1 #U1 #U2 * #c #Hc #H elim (cpg_inv_appl1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct
  elim (isrt_inv_max … Hc) -Hc #nV #nT #HcV #HcT #H destruct
  elim (isrt_inv_shift … HcV) -HcV #HcV #H destruct
  /4 width=5 by or3_intro0, ex3_2_intro, ex2_intro/
| #cV #cW #cT #p #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #H1 #H2 #H3 destruct
  lapply (isrt_inv_plus_O_dx … Hc ?) -Hc // #Hc
  elim (isrt_inv_max … Hc) -Hc #n0 #nT #Hc #HcT #H destruct
  elim (isrt_inv_max … Hc) -Hc #nV #nW #HcV #HcW #H destruct
  elim (isrt_inv_shift … HcV) -HcV #HcV #H destruct
  elim (isrt_inv_shift … HcW) -HcW #HcW #H destruct
  /4 width=11 by or3_intro1, ex5_6_intro, ex2_intro/
| #cV #cW #cT #p #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #H1 #H2 #H3 destruct
  lapply (isrt_inv_plus_O_dx … Hc ?) -Hc // #Hc
  elim (isrt_inv_max … Hc) -Hc #n0 #nT #Hc #HcT #H destruct
  elim (isrt_inv_max … Hc) -Hc #nV #nW #HcV #HcW #H destruct
  elim (isrt_inv_shift … HcV) -HcV #HcV #H destruct
  elim (isrt_inv_shift … HcW) -HcW #HcW #H destruct
  /4 width=13 by or3_intro2, ex6_7_intro, ex2_intro/
]
qed-.

lemma cpm_inv_cast1 (h) (n) (G) (L):
      ∀V1,U1,U2. ❨G,L❩ ⊢ ⓝV1.U1 ➡[h,n] U2 →
      ∨∨ ∃∃V2,T2. ❨G,L❩ ⊢ V1 ➡[h,n] V2 & ❨G,L❩ ⊢ U1 ➡[h,n] T2 & U2 = ⓝV2.T2
       | ❨G,L❩ ⊢ U1 ➡[h,n] U2
       | ∃∃m. ❨G,L❩ ⊢ V1 ➡[h,m] U2 & n = ↑m.
#h #n #G #L #V1 #U1 #U2 * #c #Hc #H elim (cpg_inv_cast1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #HcVT #H1 #H2 destruct
  elim (isrt_inv_max … Hc) -Hc #nV #nT #HcV #HcT #H destruct
  lapply (isrt_eq_t_trans … HcV HcVT) -HcVT #H
  lapply (isrt_inj … H HcT) -H #H destruct <idempotent_max
  /4 width=5 by or3_intro0, ex3_2_intro, ex2_intro/
| #cU #U12 #H destruct
  /4 width=3 by isrt_inv_plus_O_dx, or3_intro1, ex2_intro/
| #cU #H12 #H destruct
  elim (isrt_inv_plus_SO_dx … Hc) -Hc // #m #Hc #H destruct
  /4 width=3 by or3_intro2, ex2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: includes: cpr_fwd_bind1_minus *)
lemma cpm_fwd_bind1_minus (h) (n) (G) (L):
      ∀I,V1,T1,T. ❨G,L❩ ⊢ -ⓑ[I]V1.T1 ➡[h,n] T → ∀p.
      ∃∃V2,T2. ❨G,L❩ ⊢ ⓑ[p,I]V1.T1 ➡[h,n] ⓑ[p,I]V2.T2 & T = -ⓑ[I]V2.T2.
#h #n #G #L #I #V1 #T1 #T * #c #Hc #H #p elim (cpg_fwd_bind1_minus … H p) -H
/3 width=4 by ex2_2_intro, ex2_intro/
qed-.

(* Basic eliminators ********************************************************)

lemma cpm_ind (h) (Q:relation5 …):
      (∀I,G,L. Q 0 G L (⓪[I]) (⓪[I])) →
      (∀G,L,s. Q 1 G L (⋆s) (⋆(⫯[h]s))) →
      (∀n,G,K,V1,V2,W2. ❨G,K❩ ⊢ V1 ➡[h,n] V2 → Q n G K V1 V2 →
        ⇧[1] V2 ≘ W2 → Q n G (K.ⓓV1) (#0) W2
      ) → (∀n,G,K,V1,V2,W2. ❨G,K❩ ⊢ V1 ➡[h,n] V2 → Q n G K V1 V2 →
        ⇧[1] V2 ≘ W2 → Q (↑n) G (K.ⓛV1) (#0) W2
      ) → (∀n,I,G,K,T,U,i. ❨G,K❩ ⊢ #i ➡[h,n] T → Q n G K (#i) T →
        ⇧[1] T ≘ U → Q n G (K.ⓘ[I]) (#↑i) (U)
      ) → (∀n,p,I,G,L,V1,V2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 → ❨G,L.ⓑ[I]V1❩ ⊢ T1 ➡[h,n] T2 →
        Q 0 G L V1 V2 → Q n G (L.ⓑ[I]V1) T1 T2 → Q n G L (ⓑ[p,I]V1.T1) (ⓑ[p,I]V2.T2)
      ) → (∀n,G,L,V1,V2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 → ❨G,L❩ ⊢ T1 ➡[h,n] T2 →
        Q 0 G L V1 V2 → Q n G L T1 T2 → Q n G L (ⓐV1.T1) (ⓐV2.T2)
      ) → (∀n,G,L,V1,V2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,n] V2 → ❨G,L❩ ⊢ T1 ➡[h,n] T2 →
        Q n G L V1 V2 → Q n G L T1 T2 → Q n G L (ⓝV1.T1) (ⓝV2.T2)
      ) → (∀n,G,L,V,T1,T,T2. ⇧[1] T ≘ T1 → ❨G,L❩ ⊢ T ➡[h,n] T2 →
        Q n G L T T2 → Q n G L (+ⓓV.T1) T2
      ) → (∀n,G,L,V,T1,T2. ❨G,L❩ ⊢ T1 ➡[h,n] T2 →
        Q n G L T1 T2 → Q n G L (ⓝV.T1) T2
      ) → (∀n,G,L,V1,V2,T. ❨G,L❩ ⊢ V1 ➡[h,n] V2 →
        Q n G L V1 V2 → Q (↑n) G L (ⓝV1.T) V2
      ) → (∀n,p,G,L,V1,V2,W1,W2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V2 → ❨G,L❩ ⊢ W1 ➡[h,0] W2 → ❨G,L.ⓛW1❩ ⊢ T1 ➡[h,n] T2 →
        Q 0 G L V1 V2 → Q 0 G L W1 W2 → Q n G (L.ⓛW1) T1 T2 →
        Q n G L (ⓐV1.ⓛ[p]W1.T1) (ⓓ[p]ⓝW2.V2.T2)
      ) → (∀n,p,G,L,V1,V,V2,W1,W2,T1,T2. ❨G,L❩ ⊢ V1 ➡[h,0] V → ❨G,L❩ ⊢ W1 ➡[h,0] W2 → ❨G,L.ⓓW1❩ ⊢ T1 ➡[h,n] T2 →
        Q 0 G L V1 V → Q 0 G L W1 W2 → Q n G (L.ⓓW1) T1 T2 →
        ⇧[1] V ≘ V2 → Q n G L (ⓐV1.ⓓ[p]W1.T1) (ⓓ[p]W2.ⓐV2.T2)
      ) →
      ∀n,G,L,T1,T2. ❨G,L❩ ⊢ T1 ➡[h,n] T2 → Q n G L T1 T2.
#h #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #IH9 #IH10 #IH11 #IH12 #IH13 #n #G #L #T1 #T2
* #c #HC #H generalize in match HC; -HC generalize in match n; -n
elim H -c -G -L -T1 -T2
[ #I #G #L #n #H <(isrt_inv_00 … H) -H //
| #G #L #s1 #s2 #HRs #n #H <(isrt_inv_01 … H) -H destruct //
| /3 width=4 by ex2_intro/
| #c #G #L #V1 #V2 #W2 #HV12 #HVW2 #IH #x #H
  elim (isrt_inv_plus_SO_dx … H) -H // #n #Hc #H destruct
  /3 width=4 by ex2_intro/
| /3 width=4 by ex2_intro/
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #IHV #IHT #n #H
  elim (isrt_inv_max_shift_sn … H) -H #HcV #HcT
  /3 width=3 by ex2_intro/
| #cV #cT #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #IHV #IHT #n #H
  elim (isrt_inv_max_shift_sn … H) -H #HcV #HcT
  /3 width=3 by ex2_intro/
| #cU #cT #G #L #U1 #U2 #T1 #T2 #HUT #HU12 #HT12 #IHU #IHT #n #H
  elim (isrt_inv_max_eq_t … H) -H // #HcV #HcT
  /3 width=3 by ex2_intro/
| #c #G #L #V #T1 #T #T2 #HT1 #HT2 #IH #n #H
  lapply (isrt_inv_plus_O_dx … H ?) -H // #Hc
  /3 width=4 by ex2_intro/
| #c #G #L #U #T1 #T2 #HT12 #IH #n #H
  lapply (isrt_inv_plus_O_dx … H ?) -H // #Hc
  /3 width=3 by ex2_intro/
| #c #G #L #U1 #U2 #T #HU12 #IH #x #H
  elim (isrt_inv_plus_SO_dx … H) -H // #n #Hc #H destruct
  /3 width=3 by ex2_intro/
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #IHV #IHW #IHT #n #H
  lapply (isrt_inv_plus_O_dx … H ?) -H // >max_shift #H
  elim (isrt_inv_max_shift_sn … H) -H #H #HcT
  elim (isrt_O_inv_max … H) -H #HcV #HcW
  /3 width=3 by ex2_intro/
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #IHV #IHW #IHT #n #H
  lapply (isrt_inv_plus_O_dx … H ?) -H // >max_shift #H
  elim (isrt_inv_max_shift_sn … H) -H #H #HcT
  elim (isrt_O_inv_max … H) -H #HcV #HcW
  /3 width=4 by ex2_intro/
]
qed-.
