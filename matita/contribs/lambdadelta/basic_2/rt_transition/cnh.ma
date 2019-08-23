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
include "static_2/syntax/theq.ma".
include "basic_2/rt_transition/cpm.ma".

(* NORMAL TERMS FOR HEAD T-UNUNBOUND RT-TRANSITION **************************)

definition cnh (h) (G) (L): predicate term ≝
           λT1. ∀n,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → T1 ⩳ T2.

interpretation
   "normality for head t-unbound context-sensitive parallel rt-transition (term)"
   'PRedITNormal h G L T = (cnh h G L T).

(* Basic properties *********************************************************)

lemma cnh_sort (h) (G) (L): ∀s. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃⋆s⦄.
#h #G #L #s1 #n #X #H
elim (cpm_inv_sort1 … H) -H #H #_ destruct //
qed.

lemma cnh_ctop (h) (G): ∀i. ⦃G,⋆⦄ ⊢ ⥲[h] 𝐍⦃#i⦄.
#h #G * [| #i ] #n #X #H
[ elim (cpm_inv_zero1 … H) -H *
  [ #H #_ destruct //
  | #Y #X1 #X2 #_ #_ #H destruct
  | #m #Y #X1 #X2 #_ #_ #H destruct
  ]
| elim (cpm_inv_lref1 … H) -H *
  [ #H #_ destruct //
  | #Z #Y #X0 #_ #_ #H destruct
  ]
]
qed.

lemma cnh_zero (h) (G) (L): ∀I. ⦃G,L.ⓤ{I}⦄ ⊢ ⥲[h] 𝐍⦃#0⦄.
#h #G #L #I #n #X #H 
elim (cpm_inv_zero1 … H) -H *
[ #H #_ destruct //
| #Y #X1 #X2 #_ #_ #H destruct
| #m #Y #X1 #X2 #_ #_ #H destruct
]
qed.

lemma cnh_gref (h) (G) (L): ∀l. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃§l⦄.
#h #G #L #l1 #n #X #H
elim (cpm_inv_gref1 … H) -H #H #_ destruct //
qed.

lemma cnh_abst (h) (p) (G) (L): ∀W,T. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃ⓛ{p}W.T⦄.
#h #p #G #L #W1 #T1 #n #X #H
elim (cpm_inv_abst1 … H) -H #W2 #T2 #_ #_ #H destruct
/1 width=1 by theq_pair/
qed.

lemma cnh_abbr_neg (h) (G) (L): ∀V,T. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃-ⓓV.T⦄.
#h #G #L #V1 #T1 #n #X #H
elim (cpm_inv_abbr1 … H) -H *
[ #W2 #T2 #_ #_ #H destruct /1 width=1 by theq_pair/
| #X1 #_ #_ #H destruct
]
qed.
