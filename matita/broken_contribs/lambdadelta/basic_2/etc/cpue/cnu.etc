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
include "static_2/syntax/tueq.ma".
include "basic_2/rt_transition/cpm.ma".

(* NORMAL TERMS FOR T-UNUNBOUND RT-TRANSITION *******************************)

definition cnu (h) (G) (L): predicate term ≝
           λT1. ∀n,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → T1 ≅ T2.

interpretation
   "normality for t-unbound context-sensitive parallel rt-transition (term)"
   'PRedITNormal h G L T = (cnu h G L T).

(* Basic properties *********************************************************)

lemma cnu_sort (h) (G) (L): ∀s. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃⋆s⦄.
#h #G #L #s1 #n #X #H
elim (cpm_inv_sort1 … H) -H #H #_ destruct //
qed.

lemma cnu_ctop (h) (G): ∀i. ⦃G,⋆⦄ ⊢ ⥲[h] 𝐍⦃#i⦄.
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

lemma cnu_zero (h) (G) (L): ∀I. ⦃G,L.ⓤ{I}⦄ ⊢ ⥲[h] 𝐍⦃#0⦄.
#h #G #L #I #n #X #H 
elim (cpm_inv_zero1 … H) -H *
[ #H #_ destruct //
| #Y #X1 #X2 #_ #_ #H destruct
| #m #Y #X1 #X2 #_ #_ #H destruct
]
qed.

lemma cnu_gref (h) (G) (L): ∀l. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃§l⦄.
#h #G #L #l1 #n #X #H
elim (cpm_inv_gref1 … H) -H #H #_ destruct //
qed.
