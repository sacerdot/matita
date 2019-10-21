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

include "basic_2/notation/relations/pconveta_5.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* avtivate genv *)
inductive cpce (h): relation4 genv lenv term term ≝
| cpce_sort: ∀G,L,s. cpce h G L (⋆s) (⋆s)
| cpce_atom: ∀G,i. cpce h G (⋆) (#i) (#i)
| cpce_unit: ∀I,G,K. cpce h G (K.ⓤ{I}) (#0) (#0)
| cpce_ldef: ∀G,K,V. cpce h G (K.ⓓV) (#0) (#0)
| cpce_ldec: ∀G,K,W. (∀n,p,V,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
             cpce h G (K.ⓛW) (#0) (#0)
| cpce_eta : ∀n,p,G,K,W,W1,W2,V,V1,V2,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U →
             cpce h G K W W1 → ⇧*[1] W1 ≘ W2 →
             cpce h G K V V1 → ⇧*[1] V1 ≘ V2 →
             cpce h G (K.ⓛW) (#0) (ⓝW2.+ⓛV2.ⓐ#0.#1)
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

lemma cpce_inv_sort_sn (h) (G) (L) (s):
      ∀X2. ⦃G,L⦄ ⊢ ⋆s ⬌η[h] X2 → ⋆s = X2.
#h #G #Y #s0 #X2
@(insert_eq_0 … (⋆s0)) #X1 * -G -Y -X1 -X2
[ #G #L #s #_ //
| #G #i #_ //
| #I #G #K #_ //
| #G #K #V #_ //
| #G #K #W #_ #_ //
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_atom_sn (h) (G) (i):
      ∀X2. ⦃G,⋆⦄ ⊢ #i ⬌η[h] X2 → #i = X2.
#h #G #i0 #X2
@(insert_eq_0 … LAtom) #Y
@(insert_eq_0 … (#i0)) #X1
* -G -Y -X1 -X2
[ #G #L #s #_ #_ //
| #G #i #_ #_ //
| #I #G #K #_ #_ //
| #G #K #V #_ #_ //
| #G #K #W #_ #_ #_ //
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #_ #H destruct
| #G #L #l #_ #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_unit_sn (h) (I) (G) (K):
      ∀X2. ⦃G,K.ⓤ{I}⦄ ⊢ #0 ⬌η[h] X2 → #0 = X2.
#h #I0 #G #K0 #X2
@(insert_eq_0 … (K0.ⓤ{I0})) #Y
@(insert_eq_0 … (#0)) #X1
* -G -Y -X1 -X2
[ #G #L #s #_ #_ //
| #G #i #_ #_ //
| #I #G #K #_ #_ //
| #G #K #V #_ #_ //
| #G #K #W #_ #_ #_ //
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H #_ destruct
| #G #L #l #_ #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_ldef_sn (h) (G) (K) (V):
      ∀X2. ⦃G,K.ⓓV⦄ ⊢ #0 ⬌η[h] X2 → #0 = X2.
#h #G #K0 #V0 #X2
@(insert_eq_0 … (K0.ⓓV0)) #Y
@(insert_eq_0 … (#0)) #X1
* -G -Y -X1 -X2
[ #G #L #s #_ #_ //
| #G #i #_ #_ //
| #I #G #K #_ #_ //
| #G #K #V #_ #_ //
| #G #K #W #_ #_ #_ //
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H #_ destruct
| #G #L #l #_ #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_ldec_sn (h) (G) (K) (W):
      ∀X2. ⦃G,K.ⓛW⦄ ⊢ #0 ⬌η[h] X2 →
      ∨∨ ∧∧ ∀n,p,V,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥ & #0 = X2
       | ∃∃n,p,W1,W2,V,V1,V2,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U
                              & ⦃G,K⦄ ⊢ W ⬌η[h] W1 & ⇧*[1] W1 ≘ W2
                              & ⦃G,K⦄ ⊢ V ⬌η[h] V1 & ⇧*[1] V1 ≘ V2
                              & ⓝW2.+ⓛV2.ⓐ#0.#1 = X2.
#h #G #K0 #W0 #X2
@(insert_eq_0 … (K0.ⓛW0)) #Y
@(insert_eq_0 … (#0)) #X1
* -G -Y -X1 -X2
[ #G #L #s #H #_ destruct
| #G #i #_ #H destruct
| #I #G #K #_ #H destruct
| #G #K #V #_ #H destruct
| #G #K #W #HW #_ #H destruct /4 width=5 by or_introl, conj/
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #HWU #HW1 #HW12 #HV1 #HV12 #_ #H destruct
  /3 width=14 by or_intror, ex6_8_intro/
| #I #G #K #T #U #i #_ #_ #H #_ destruct
| #G #L #l #H #_ destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_lref_sn (h) (I) (G) (K) (i):
      ∀X2. ⦃G,K.ⓘ{I}⦄ ⊢ #↑i ⬌η[h] X2 →
      ∃∃T2. ⦃G,K⦄ ⊢ #i ⬌η[h] T2 & ⇧*[1] T2 ≘ X2.
#h #I0 #G #K0 #i0 #X2
@(insert_eq_0 … (K0.ⓘ{I0})) #Y
@(insert_eq_0 … (#↑i0)) #X1
* -G -Y -X1 -X2
[ #G #L #s #H #_ destruct
| #G #i #_ #H destruct
| #I #G #K #H #_ destruct
| #G #K #V #H #_ destruct
| #G #K #W #_ #H #_ destruct
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #H #_ destruct
| #I #G #K #T #U #i #Hi #HTU #H1 #H2 destruct /2 width=3 by ex2_intro/
| #G #L #l #H #_ destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H #_ destruct
]
qed-.

lemma cpce_inv_gref_sn (h) (G) (L) (l):
      ∀X2. ⦃G,L⦄ ⊢ §l ⬌η[h] X2 → §l = X2.
#h #G #Y #l0 #X2
@(insert_eq_0 … (§l0)) #X1 * -G -Y -X1 -X2
[ #G #L #s #_ //
| #G #i #_ //
| #I #G #K #_ //
| #G #K #V #_ //
| #G #K #W #_ #_ //
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #_ //
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_bind_sn (h) (p) (I) (G) (K) (V1) (T1):
      ∀X2. ⦃G,K⦄ ⊢ ⓑ{p,I}V1.T1 ⬌η[h] X2 →
      ∃∃V2,T2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 & ⦃G,K.ⓑ{I}V1⦄ ⊢ T1 ⬌η[h] T2 & ⓑ{p,I}V2.T2 = X2.
#h #p0 #I0 #G #Y #V0 #T0 #X2
@(insert_eq_0 … (ⓑ{p0,I0}V0.T0)) #X1 * -G -Y -X1 -X2
[ #G #L #s #H destruct
| #G #i #H destruct
| #I #G #K #H destruct
| #G #K #V #H destruct
| #G #K #W #_ #H destruct
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #H destruct
| #p #I #G #K #V1 #V2 #T1 #T2 #HV #HT #H destruct /2 width=5 by ex3_2_intro/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
]
qed-.

lemma cpce_inv_flat_sn (h) (I) (G) (L) (V1) (T1):
      ∀X2. ⦃G,L⦄ ⊢ ⓕ{I}V1.T1 ⬌η[h] X2 →
      ∃∃V2,T2. ⦃G,L⦄ ⊢ V1 ⬌η[h] V2 & ⦃G,L⦄ ⊢ T1 ⬌η[h] T2 & ⓕ{I}V2.T2 = X2.
#h #I0 #G #Y #V0 #T0 #X2
@(insert_eq_0 … (ⓕ{I0}V0.T0)) #X1 * -G -Y -X1 -X2
[ #G #L #s #H destruct
| #G #i #H destruct
| #I #G #K #H destruct
| #G #K #V #H destruct
| #G #K #W #_ #H destruct
| #n #p #G #K #W #W1 #W2 #V #V1 #V2 #U #_ #_ #_ #_ #_ #H destruct
| #I #G #K #T #U #i #_ #_ #H destruct
| #G #L #l #H destruct
| #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #H destruct
| #I #G #K #V1 #V2 #T1 #T2 #HV #HT #H destruct /2 width=5 by ex3_2_intro/
]
qed-.
