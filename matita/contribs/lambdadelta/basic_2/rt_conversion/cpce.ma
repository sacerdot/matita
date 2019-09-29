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

include "ground_2/xoa/ex_5_7.ma".
include "basic_2/notation/relations/pconveta_5.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* avtivate genv *)
inductive cpce (h): relation4 genv lenv term term ≝
| cpce_sort: ∀G,L,s. cpce h G L (⋆s) (⋆s)
| cpce_atom: ∀G,i. cpce h G (⋆) (#i) (#i)
| cpce_zero: ∀G,K,I. (∀n,p,W,V,U. I = BPair Abst W → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
             cpce h G (K.ⓘ{I}) (#0) (#0)
| cpce_eta : ∀n,p,G,K,W,V1,V2,W2,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U →
             cpce h G K V1 V2 → ⇧*[1] V2 ≘ W2 → cpce h G (K.ⓛW) (#0) (+ⓛW2.ⓐ#0.#1)
| cpce_lref: ∀I,G,K,T,U,i. cpce h G K (#i) T →
             ⇧*[1] T ≘ U → cpce h G (K.ⓘ{I}) (#↑i) U
| cpce_gref: ∀G,L,l. cpce h G L (§l) (§l)
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
| #G #i #_ //
| #G #K #I #_ #_ //
| #n #p #G #K #W #V1 #V2 #W2 #U #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_atom_sn (h) (G) (X2):
      ∀i. ⦃G,⋆⦄ ⊢ #i ⬌η[h] X2 → #i = X2.
#h #G #X2 #j
@(insert_eq_0 … LAtom) #Y
@(insert_eq_0 … (#j)) #X1
* -G -Y -X1 -X2
[ #G #L #s #_ #_ //
| #G #i #_ #_ //
| #G #K #I #_ #_ #_ //
| #n #p #G #K #W #V1 #V2 #W2 #U #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #_ #H destruct
| #G #L #l #_ #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_zero_sn (h) (G) (K) (X2):
      ∀I. ⦃G,K.ⓘ{I}⦄ ⊢ #0 ⬌η[h] X2 →
      ∨∨ ∧∧ ∀n,p,W,V,U. I = BPair Abst W → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥ & #0 = X2
       | ∃∃n,p,W,V1,V2,W2,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U & ⦃G,K⦄ ⊢ V1 ⬌η[h] V2
                           & ⇧*[1] V2 ≘ W2 & I = BPair Abst W & +ⓛW2.ⓐ#0.#1 = X2.
#h #G #Y0 #X2 #Z
@(insert_eq_0 … (Y0.ⓘ{Z})) #Y
@(insert_eq_0 … (#0)) #X1
* -G -Y -X1 -X2
[ #G #L #s #H #_ destruct
| #G #i #_ #H destruct
| #G #K #I #HI #_ #H destruct /4 width=7 by or_introl, conj/
| #n #p #G #K #W #V1 #V2 #W2 #U #HWU #HV12 #HVW2 #_ #H destruct /3 width=12 by or_intror, ex5_7_intro/
| #I #G #K #T #U #i #_ #_ #H #_ destruct
| #G #L #l #H #_ destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_lref_sn (h) (G) (K) (X2):
      ∀I,i. ⦃G,K.ⓘ{I}⦄ ⊢ #↑i ⬌η[h] X2 →
      ∃∃T2. ⦃G,K⦄ ⊢ #i ⬌η[h] T2 & ⇧*[1] T2 ≘ X2.
#h #G #Y0 #X2 #Z #j
@(insert_eq_0 … (Y0.ⓘ{Z})) #Y
@(insert_eq_0 … (#↑j)) #X1
* -G -Y -X1 -X2
[ #G #L #s #H #_ destruct
| #G #i #_ #H destruct
| #G #K #I #_ #H #_ destruct
| #n #p #G #K #W #V1 #V2 #W2 #U #_ #_ #_ #H #_ destruct
| #I #G #K #T #U #i #Hi #HTU #H1 #H2 destruct /2 width=3 by ex2_intro/
| #G #L #l #H #_ destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_gref_sn (h) (G) (L) (X2):
      ∀l. ⦃G,L⦄ ⊢ §l ⬌η[h] X2 → §l = X2.
#h #G #Y #X2 #k
@(insert_eq_0 … (§k)) #X1 * -G -Y -X1 -X2
[ #G #L #s #_ //
| #G #i #_ //
| #G #K #I #_ #_ //
| #n #p #G #K #W #V1 #V2 #W2 #U #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_bind_sn (h) (G) (K) (X2):
      ∀p,I,V1,T1. ⦃G,K⦄ ⊢ ⓑ{p,I}V1.T1 ⬌η[h] X2 →
      ∃∃V2,T2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 & ⦃G,K.ⓑ{I}V1⦄ ⊢ T1 ⬌η[h] T2 & ⓑ{p,I}V2.T2 = X2.
#h #G #Y #X2 #q #Z #U #X
@(insert_eq_0 … (ⓑ{q,Z}U.X)) #X1 * -G -Y -X1 -X2
[ #G #L #s #H destruct
| #G #i #H destruct
| #G #K #I #_ #H destruct
| #n #p #G #K #W #V1 #V2 #W2 #U #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #H destruct
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
| #G #i #H destruct
| #G #K #I #_ #H destruct
| #n #p #G #K #W #V1 #V2 #W2 #U #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #H destruct
| #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #K #V1 #V2 #T1 #T2 #HV #HT #H destruct /2 width=5 by ex3_2_intro/
]
qed-.
