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

include "ground_2/xoa/ex_4_3.ma".
include "ground_2/steps/rtc_ist_shift.ma".
include "ground_2/steps/rtc_ist_plus.ma".
include "ground_2/steps/rtc_ist_max.ma".
include "basic_2/notation/relations/pty_6.ma".
include "basic_2/rt_transition/cpg.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

definition cpt (h) (G) (L) (n): relation2 term term ≝
           λT1,T2. ∃∃c. 𝐓❪n,c❫ & ❪G,L❫ ⊢ T1 ⬈[eq …,c,h] T2.

interpretation
  "t-bound context-sensitive parallel t-transition (term)"
  'PTy h n G L T1 T2 = (cpt h G L n T1 T2).

(* Basic properties *********************************************************)

lemma cpt_ess (h) (G) (L):
      ∀s. ❪G,L❫ ⊢ ⋆s ⬆[h,1] ⋆(⫯[h]s).
/2 width=3 by cpg_ess, ex2_intro/ qed.

lemma cpt_delta (h) (n) (G) (K):
      ∀V1,V2. ❪G,K❫ ⊢ V1 ⬆[h,n] V2 →
      ∀W2. ⇧[1] V2 ≘ W2 → ❪G,K.ⓓV1❫ ⊢ #0 ⬆[h,n] W2.
#h #n #G #K #V1 #V2 *
/3 width=5 by cpg_delta, ex2_intro/
qed.

lemma cpt_ell (h) (n) (G) (K):
      ∀V1,V2. ❪G,K❫ ⊢ V1 ⬆[h,n] V2 →
      ∀W2. ⇧[1] V2 ≘ W2 → ❪G,K.ⓛV1❫ ⊢ #0 ⬆[h,↑n] W2.
#h #n #G #K #V1 #V2 *
/3 width=5 by cpg_ell, ex2_intro, ist_succ/
qed.

lemma cpt_lref (h) (n) (G) (K):
      ∀T,i. ❪G,K❫ ⊢ #i ⬆[h,n] T → ∀U. ⇧[1] T ≘ U →
      ∀I. ❪G,K.ⓘ[I]❫ ⊢ #↑i ⬆[h,n] U.
#h #n #G #K #T #i *
/3 width=5 by cpg_lref, ex2_intro/
qed.

lemma cpt_bind (h) (n) (G) (L):
      ∀V1,V2. ❪G,L❫ ⊢ V1 ⬆[h,0] V2 → ∀I,T1,T2. ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬆[h,n] T2 →
      ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬆[h,n] ⓑ[p,I]V2.T2.
#h #n #G #L #V1 #V2 * #cV #HcV #HV12 #I #T1 #T2 *
/3 width=5 by cpg_bind, ist_max_O1, ex2_intro/
qed.

lemma cpt_appl (h) (n) (G) (L):
      ∀V1,V2. ❪G,L❫ ⊢ V1 ⬆[h,0] V2 →
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆[h,n] T2 → ❪G,L❫ ⊢ ⓐV1.T1 ⬆[h,n] ⓐV2.T2.
#h #n #G #L #V1 #V2 * #cV #HcV #HV12 #T1 #T2 *
/3 width=5 by ist_max_O1, cpg_appl, ex2_intro/
qed.

lemma cpt_cast (h) (n) (G) (L):
      ∀U1,U2. ❪G,L❫ ⊢ U1 ⬆[h,n] U2 →
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆[h,n] T2 → ❪G,L❫ ⊢ ⓝU1.T1 ⬆[h,n] ⓝU2.T2.
#h #n #G #L #U1 #U2 * #cU #HcU #HU12 #T1 #T2 *
/3 width=6 by cpg_cast, ex2_intro/
qed.

lemma cpt_ee (h) (n) (G) (L):
      ∀U1,U2. ❪G,L❫ ⊢ U1 ⬆[h,n] U2 → ∀T. ❪G,L❫ ⊢ ⓝU1.T ⬆[h,↑n] U2.
#h #n #G #L #V1 #V2 *
/3 width=3 by cpg_ee, ist_succ, ex2_intro/
qed.

lemma cpt_refl (h) (G) (L): reflexive … (cpt h G L 0).
/3 width=3 by cpg_refl, ex2_intro/ qed.

(* Advanced properties ******************************************************)

lemma cpt_sort (h) (G) (L):
      ∀n. n ≤ 1 → ∀s. ❪G,L❫ ⊢ ⋆s ⬆[h,n] ⋆((next h)^n s).
#h #G #L * //
#n #H #s <(le_n_O_to_eq n) /2 width=1 by le_S_S_to_le/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpt_inv_atom_sn (h) (n) (J) (G) (L):
      ∀X2. ❪G,L❫ ⊢ ⓪[J] ⬆[h,n] X2 →
      ∨∨ ∧∧ X2 = ⓪[J] & n = 0
       | ∃∃s. X2 = ⋆(⫯[h]s) & J = Sort s & n =1
       | ∃∃K,V1,V2. ❪G,K❫ ⊢ V1 ⬆[h,n] V2 & ⇧[1] V2 ≘ X2 & L = K.ⓓV1 & J = LRef 0
       | ∃∃m,K,V1,V2. ❪G,K❫ ⊢ V1 ⬆[h,m] V2 & ⇧[1] V2 ≘ X2 & L = K.ⓛV1 & J = LRef 0 & n = ↑m
       | ∃∃I,K,T,i. ❪G,K❫ ⊢ #i ⬆[h,n] T & ⇧[1] T ≘ X2 & L = K.ⓘ[I] & J = LRef (↑i).
#h #n #J #G #L #X2 * #c #Hc #H
elim (cpg_inv_atom1 … H) -H *
[ #H1 #H2 destruct /3 width=1 by or5_intro0, conj/
| #s #H1 #H2 #H3 destruct /3 width=3 by or5_intro1, ex3_intro/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 #H3 destruct
  /4 width=6 by or5_intro2, ex4_3_intro, ex2_intro/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 #H3 destruct
  elim (ist_inv_plus_SO_dx … H3) -H3 [| // ] #m #Hc #H destruct
  /4 width=9 by or5_intro3, ex5_4_intro, ex2_intro/
| #I #K #V2 #i #HV2 #HVT2 #H1 #H2 destruct
  /4 width=8 by or5_intro4, ex4_4_intro, ex2_intro/
]
qed-.

lemma cpt_inv_sort_sn (h) (n) (G) (L) (s):
      ∀X2. ❪G,L❫ ⊢ ⋆s ⬆[h,n] X2 →
      ∧∧ X2 = ⋆(((next h)^n) s) & n ≤ 1.
#h #n #G #L #s #X2 * #c #Hc #H
elim (cpg_inv_sort1 … H) -H * #H1 #H2 destruct
/2 width=1 by conj/
qed-.

lemma cpt_inv_zero_sn (h) (n) (G) (L):
      ∀X2. ❪G,L❫ ⊢ #0 ⬆[h,n] X2 →
      ∨∨ ∧∧ X2 = #0 & n = 0
       | ∃∃K,V1,V2. ❪G,K❫ ⊢ V1 ⬆[h,n] V2 & ⇧[1] V2 ≘ X2 & L = K.ⓓV1
       | ∃∃m,K,V1,V2. ❪G,K❫ ⊢ V1 ⬆[h,m] V2 & ⇧[1] V2 ≘ X2 & L = K.ⓛV1 & n = ↑m.
#h #n #G #L #X2 * #c #Hc #H elim (cpg_inv_zero1 … H) -H *
[ #H1 #H2 destruct /4 width=1 by ist_inv_00, or3_intro0, conj/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 destruct
  /4 width=8 by or3_intro1, ex3_3_intro, ex2_intro/
| #cV #K #V1 #V2 #HV12 #HVT2 #H1 #H2 destruct
  elim (ist_inv_plus_SO_dx … H2) -H2 // #m #Hc #H destruct
  /4 width=8 by or3_intro2, ex4_4_intro, ex2_intro/
]
qed-.

lemma cpt_inv_zero_sn_unit (h) (n) (I) (K) (G):
      ∀X2. ❪G,K.ⓤ[I]❫ ⊢ #0 ⬆[h,n] X2 → ∧∧ X2 = #0 & n = 0.
#h #n #I #G #K #X2 #H
elim (cpt_inv_zero_sn … H) -H *
[ #H1 #H2 destruct /2 width=1 by conj/
| #Y #X1 #X2 #_ #_ #H destruct
| #m #Y #X1 #X2 #_ #_ #H destruct
]
qed.

lemma cpt_inv_lref_sn (h) (n) (G) (L) (i):
      ∀X2. ❪G,L❫ ⊢ #↑i ⬆[h,n] X2 →
      ∨∨ ∧∧ X2 = #(↑i) & n = 0
       | ∃∃I,K,T. ❪G,K❫ ⊢ #i ⬆[h,n] T & ⇧[1] T ≘ X2 & L = K.ⓘ[I].
#h #n #G #L #i #X2 * #c #Hc #H elim (cpg_inv_lref1 … H) -H *
[ #H1 #H2 destruct /4 width=1 by ist_inv_00, or_introl, conj/
| #I #K #V2 #HV2 #HVT2 #H destruct
 /4 width=6 by ex3_3_intro, ex2_intro, or_intror/
]
qed-.

lemma cpt_inv_lref_sn_ctop (n) (h) (G) (i):
      ∀X2. ❪G,⋆❫ ⊢ #i ⬆[h,n] X2 → ∧∧ X2 = #i & n = 0.
#h #n #G * [| #i ] #X2 #H
[ elim (cpt_inv_zero_sn … H) -H *
  [ #H1 #H2 destruct /2 width=1 by conj/
  | #Y #X1 #X2 #_ #_ #H destruct
  | #m #Y #X1 #X2 #_ #_ #H destruct
  ]
| elim (cpt_inv_lref_sn … H) -H *
  [ #H1 #H2 destruct /2 width=1 by conj/
  | #Z #Y #X0 #_ #_ #H destruct
  ]
]
qed.

lemma cpt_inv_gref_sn (h) (n) (G) (L) (l):
      ∀X2. ❪G,L❫ ⊢ §l ⬆[h,n] X2 → ∧∧ X2 = §l & n = 0.
#h #n #G #L #l #X2 * #c #Hc #H elim (cpg_inv_gref1 … H) -H
#H1 #H2 destruct /2 width=1 by conj/
qed-.

lemma cpt_inv_bind_sn (h) (n) (p) (I) (G) (L) (V1) (T1):
      ∀X2. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬆[h,n] X2 →
      ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬆[h,0] V2 & ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬆[h,n] T2
             & X2 = ⓑ[p,I]V2.T2.
#h #n #p #I #G #L #V1 #T1 #X2 * #c #Hc #H
elim (cpg_inv_bind1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct
  elim (ist_inv_max … H2) -H2 #nV #nT #HcV #HcT #H destruct
  elim (ist_inv_shift … HcV) -HcV #HcV #H destruct
  /3 width=5 by ex3_2_intro, ex2_intro/
| #cT #T2 #_ #_ #_ #_ #H destruct
  elim (ist_inv_plus_10_dx … H)
]
qed-.

lemma cpt_inv_appl_sn (h) (n) (G) (L) (V1) (T1):
      ∀X2. ❪G,L❫ ⊢ ⓐV1.T1 ⬆[h,n] X2 →
      ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬆[h,0] V2 & ❪G,L❫ ⊢ T1 ⬆[h,n] T2 & X2 = ⓐV2.T2.
#h #n #G #L #V1 #T1 #X2 * #c #Hc #H elim (cpg_inv_appl1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct
  elim (ist_inv_max … H2) -H2 #nV #nT #HcV #HcT #H destruct
  elim (ist_inv_shift … HcV) -HcV #HcV #H destruct
  /3 width=5 by ex3_2_intro, ex2_intro/
| #cV #cW #cU #p #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #_ #H destruct
  elim (ist_inv_plus_10_dx … H)
| #cV #cW #cU #p #V #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #_ #_ #H destruct
  elim (ist_inv_plus_10_dx … H)
]
qed-.

lemma cpt_inv_cast_sn (h) (n) (G) (L) (V1) (T1):
      ∀X2. ❪G,L❫ ⊢ ⓝV1.T1 ⬆[h,n] X2 →
      ∨∨ ∃∃V2,T2. ❪G,L❫ ⊢ V1 ⬆[h,n] V2 & ❪G,L❫ ⊢ T1 ⬆[h,n] T2 & X2 = ⓝV2.T2
       | ∃∃m. ❪G,L❫ ⊢ V1 ⬆[h,m] X2 & n = ↑m.
#h #n #G #L #V1 #T1 #X2 * #c #Hc #H elim (cpg_inv_cast1 … H) -H *
[ #cV #cT #V2 #T2 #HV12 #HT12 #HcVT #H1 #H2 destruct
  elim (ist_inv_max … H2) -H2 #nV #nT #HcV #HcT #H destruct
  <idempotent_max
  /4 width=5 by or_introl, ex3_2_intro, ex2_intro/
| #cT #_ #H destruct
  elim (ist_inv_plus_10_dx … H)
| #cV #H12 #H destruct
  elim (ist_inv_plus_SO_dx … H) -H [| // ] #m #Hm #H destruct
  /4 width=3 by ex2_intro, or_intror/
]
qed-.
