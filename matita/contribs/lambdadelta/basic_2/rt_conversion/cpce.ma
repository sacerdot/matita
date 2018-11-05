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

include "ground_2/xoa/ex_2_4.ma".
include "basic_2/notation/relations/pconveta_5.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* avtivate genv *)
inductive cpce (h): relation4 genv lenv term term ≝
| cpce_sort: ∀G,L,s. cpce h G L (⋆s) (⋆s)
| cpce_ldef: ∀G,K,V. cpce h G (K.ⓓV) (#0) (#0)
| cpce_ldec: ∀n,G,K,V,s. ⦃G,K⦄ ⊢ V ➡*[n,h] ⋆s →
             cpce h G (K.ⓛV) (#0) (#0)
| cpce_eta : ∀n,p,G,K,V,W,T. ⦃G,K⦄ ⊢ V ➡*[n,h] ⓛ{p}W.T →
             cpce h G (K.ⓛV) (#0) (+ⓛW.ⓐ#0.#1)
| cpce_lref: ∀I,G,K,T,U,i. cpce h G K (#i) T →
             ⬆*[1] T ≘ U → cpce h G (K.ⓘ{I}) (#↑i) U
| cpce_bind: ∀p,I,G,K,V1,V2,T1,T2.
             cpce h G K V1 V2 → cpce h G (K.ⓑ{I}V1) T1 T2 →
             cpce h G K (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
| cpce_flat: ∀I,G,L,V1,V2,T1,T2.
             cpce h G L V1 V2 → cpce h G L T1 T2 →
             cpce h G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation
   "context-sensitive parallel eta-conversion (term)"
   'PConvEta h G L T1 T2 = (cpce h G L T1 T2).

(* Basic inversion lemmas ***************************************************)

lemma cpce_inv_sort_sn (h) (G) (L) (X2):
      ∀s. ⦃G,L⦄ ⊢ ⋆s ⬌η[h] X2 → ⋆s = X2.
#h #G #Y #X2 #s0
@(insert_eq_0 … (⋆s0)) #X1 * -G -Y -X1 -X2
[ #G #L #s #_ //
| #G #K #V #_ //
| #n #G #K #V #s #_ #_ //
| #n #p #G #K #V #W #T #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_ldef_sn (h) (G) (K) (X2):
      ∀V. ⦃G,K.ⓓV⦄ ⊢ #0 ⬌η[h] X2 → #0 = X2.
#h #G #Y #X2 #X
@(insert_eq_0 … (Y.ⓓX)) #Y1
@(insert_eq_0 … (#0)) #X1
* -G -Y1 -X1 -X2
[ #G #L #s #_ #_ //
| #G #K #V #_ #_ //
| #n #G #K #V #s #_ #_ #_ //
| #n #p #G #K #V #W #T #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H #_ destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_ldec_sn (h) (G) (K) (X2):
      ∀V. ⦃G,K.ⓛV⦄ ⊢ #0 ⬌η[h] X2 →
      ∨∨ ∃∃n,s. ⦃G,K⦄ ⊢ V ➡*[n,h] ⋆s & #0 = X2
       | ∃∃n,p,W,T. ⦃G,K⦄ ⊢ V ➡*[n,h] ⓛ{p}W.T & +ⓛW.ⓐ#0.#1 = X2.
#h #G #Y #X2 #X
@(insert_eq_0 … (Y.ⓛX)) #Y1
@(insert_eq_0 … (#0)) #X1
* -G -Y1 -X1 -X2
[ #G #L #s #H #_ destruct
| #G #K #V #_ #H destruct
| #n #G #K #V #s #HV #_ #H destruct /3 width=3 by ex2_2_intro, or_introl/
| #n #p #G #K #V #W #T #HV #_ #H destruct /3 width=6 by or_intror, ex2_4_intro/
| #I #G #K #T #U #i #_ #_ #H #_ destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_lref_sn (h) (G) (K) (X2):
      ∀I,i. ⦃G,K.ⓘ{I}⦄ ⊢ #↑i ⬌η[h] X2 →
      ∃∃T2. ⦃G,K⦄ ⊢ #i ⬌η[h] T2 & ⬆*[1] T2 ≘ X2.
#h #G #Y #X2 #Z #j
@(insert_eq_0 … (Y.ⓘ{Z})) #Y1
@(insert_eq_0 … (#↑j)) #X1
* -G -Y1 -X1 -X2
[ #G #L #s #H #_ destruct
| #G #K #V #H #_ destruct
| #n #G #K #V #s #_ #H #_ destruct
| #n #p #G #K #V #W #T #_ #H #_ destruct
| #I #G #K #T #U #i #Hi #HTU #H1 #H2 destruct /2 width=3 by ex2_intro/
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_bind_sn (h) (G) (K) (X2):
      ∀p,I,V1,T1. ⦃G,K⦄ ⊢ ⓑ{p,I}V1.T1 ⬌η[h] X2 →
      ∃∃V2,T2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 & ⦃G,K.ⓑ{I}V1⦄ ⊢ T1 ⬌η[h] T2 & ⓑ{p,I}V2.T2 = X2.
#h #G #Y #X2 #q #Z #U #X
@(insert_eq_0 … (ⓑ{q,Z}U.X)) #X1 * -G -Y -X1 -X2
[ #G #L #s #H destruct
| #G #K #V #H destruct
| #n #G #K #V #s #_ #H destruct
| #n #p #G #K #V #W #T #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #HV #HT #H destruct /2 width=5 by ex3_2_intro/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_flat_sn (h) (G) (L) (X2):
      ∀I,V1,T1. ⦃G,L⦄ ⊢ ⓕ{I}V1.T1 ⬌η[h] X2 →
      ∃∃V2,T2. ⦃G,L⦄ ⊢ V1 ⬌η[h] V2 & ⦃G,L⦄ ⊢ T1 ⬌η[h] T2 & ⓕ{I}V2.T2 = X2.
#h #G #Y #X2 #Z #U #X
@(insert_eq_0 … (ⓕ{Z}U.X)) #X1 * -G -Y -X1 -X2
[ #G #L #s #H destruct
| #G #K #V #H destruct
| #n #G #K #V #s #_ #H destruct
| #n #p #G #K #V #W #T #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #K #V1 #V2 #T1 #T2 #HV #HT #H destruct /2 width=5 by ex3_2_intro/
]
qed-.
