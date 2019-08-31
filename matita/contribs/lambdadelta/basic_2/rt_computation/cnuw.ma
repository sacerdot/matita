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

include "basic_2/notation/relations/preditnormal_4.ma".
include "static_2/syntax/tweq.ma".
include "basic_2/rt_computation/cpms.ma".

(* NORMAL TERMS FOR T-UNUNBOUND WHD RT-TRANSITION ***************************)

definition cnuw (h) (G) (L): predicate term ≝
           λT1. ∀n,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → T1 ≅ T2.

interpretation
  "normality for t-unbound weak head context-sensitive parallel rt-transition (term)"
  'PRedITNormal h G L T = (cnuw h G L T).

lemma cpm_inv_lref1_ctop (n) (h) (G):
      ∀X2,i. ⦃G,⋆⦄ ⊢ #i ➡[n,h] X2 → ∧∧ X2 = #i & n = 0.
#n #h #G #X2 * [| #i ] #H
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

lemma cpm_inv_zero1_unit (n) (h) (I) (K) (G):
      ∀X2. ⦃G,K.ⓤ{I}⦄ ⊢ #0 ➡[n,h] X2 → ∧∧ X2 = #0 & n = 0.
#n #h #I #G #K #X2 #H
elim (cpm_inv_zero1 … H) -H *
[ #H1 #H2 destruct /2 width=1 by conj/
| #Y #X1 #X2 #_ #_ #H destruct
| #m #Y #X1 #X2 #_ #_ #H destruct
]
qed.

lemma cpms_inv_lref1_ctop (n) (h) (G):
      ∀X2,i. ⦃G,⋆⦄ ⊢ #i ➡*[n,h] X2 → ∧∧ X2 = #i & n = 0.
#n #h #G #X2 #i #H @(cpms_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpm_inv_lref1_ctop … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpms_inv_zero1_unit (n) (h) (I) (K) (G):
      ∀X2. ⦃G,K.ⓤ{I}⦄ ⊢ #0 ➡*[n,h] X2 → ∧∧ X2 = #0 & n = 0.
#n #h #I #G #K #X2 #H @(cpms_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpm_inv_zero1_unit … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpms_inv_gref1 (n) (h) (G) (L):
      ∀X2,l. ⦃G,L⦄ ⊢ §l ➡*[n,h] X2 → ∧∧ X2 = §l & n = 0.
#n #h #G #L #X2 #l #H @(cpms_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpm_inv_gref1 … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

(* Basic properties *********************************************************)

lemma cnuw_sort (h) (G) (L): ∀s. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] ⋆s.
#h #G #L #s1 #n #X #H
lapply (cpms_inv_sort1 … H) -H #H destruct //
qed.

lemma cnuw_ctop (h) (G): ∀i. ⦃G,⋆⦄ ⊢ ➡𝐍𝐖*[h] #i.
#h #G #i #n #X #H
elim (cpms_inv_lref1_ctop … H) -H #H #_ destruct //
qed.

lemma cnuw_zero_unit (h) (G) (L): ∀I. ⦃G,L.ⓤ{I}⦄ ⊢ ➡𝐍𝐖*[h] #0.
#h #G #L #I #n #X #H
elim (cpms_inv_zero1_unit … H) -H #H #_ destruct //
qed.

lemma cnuw_gref (h) (G) (L): ∀l. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] §l.
#h #G #L #l1 #n #X #H
elim (cpms_inv_gref1 … H) -H #H #_ destruct //
qed.

(* Basic_inversion lemmas ***************************************************)

lemma cnuw_inv_zero_pair (h) (I) (G) (L): ∀V. ⦃G,L.ⓑ{I}V⦄ ⊢ ➡𝐍𝐖*[h] #0 → ⊥.
#h * #G #L #V #H
elim (lifts_total V (𝐔❴1❵)) #W #HVW
[ lapply (H 0 W ?) [ /3 width=3 by cpm_cpms, cpm_delta/ ]
| lapply (H 1 W ?) [ /3 width=3 by cpm_cpms, cpm_ell/ ]
] -H #HW
lapply (tweq_inv_lref_sn … HW) -HW #H destruct
/2 width=5 by lifts_inv_lref2_uni_lt/
qed-.

lemma cnuw_inv_cast (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] ⓝV.T → ⊥.
#h #G #L #V #T #H
lapply (H 0 T ?) [ /3 width=1 by cpm_cpms, cpm_eps/ ] -H #H
/2 width=3 by tweq_inv_cast_sn_XY_Y/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cnuw_fwd_appl (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] ⓐV.T → ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] T.
#h #G #L #V #T1 #HT1 #n #T2 #HT12
lapply (HT1 n (ⓐV.T2) ?) -HT1
/2 width=3 by cpms_appl_dx, tweq_inv_appl_bi/
qed-.
