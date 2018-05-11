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

include "basic_2/notation/relations/exclaim_5.ma".
include "basic_2/rt_computation/cpms.ma".

(* NATIVE VALIDITY FOR TERMS ************************************************)

(* activate genv *)
(* Basic_2A1: uses: snv *)
inductive nv (a) (h): relation3 genv lenv term ≝
| nv_sort: ∀G,L,s. nv a h G L (⋆s)
| nv_zero: ∀I,G,K,V. nv a h G K V → nv a h G (K.ⓑ{I}V) (#0)
| nv_lref: ∀I,G,K,i. nv a h G K (#i) → nv a h G (K.ⓘ{I}) (#↑i)
| nv_bind: ∀p,I,G,L,V,T. nv a h G L V → nv a h G (L.ⓑ{I}V) T → nv a h G L (ⓑ{p,I}V.T)
| nv_appl: ∀n,p,G,L,V,W0,T,U0. (a = Ⓣ → n = 1) → nv a h G L V → nv a h G L T →
           ⦃G, L⦄ ⊢ V ➡*[1, h] W0 → ⦃G, L⦄ ⊢ T ➡*[n, h] ⓛ{p}W0.U0 → nv a h G L (ⓐV.T)
| nv_cast: ∀G,L,U,T,U0. nv a h G L U → nv a h G L T →
           ⦃G, L⦄ ⊢ U ➡*[h] U0 → ⦃G, L⦄ ⊢ T ➡*[1, h] U0 → nv a h G L (ⓝU.T)
.

interpretation "native validity (term)"
   'Exclaim a h G L T = (nv a h G L T).

(* Basic inversion lemmas ***************************************************)

fact nv_inv_zero_aux (a) (h): ∀G,L,X. ⦃G, L⦄ ⊢ X ![a, h] → X = #0 →
                              ∃∃I,K,V. ⦃G, K⦄ ⊢ V ![a, h] & L = K.ⓑ{I}V.
#a #h #G #L #X * -G -L -X
[ #G #L #s #H destruct
| #I #G #K #V #HV #_ /2 width=5 by ex2_3_intro/
| #I #G #K #i #_ #H destruct
| #p #I #G #L #V #T #_ #_ #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #H destruct
]
qed-.

lemma nv_inv_zero (a) (h): ∀G,L. ⦃G, L⦄ ⊢ #0 ![a, h] →
                           ∃∃I,K,V. ⦃G, K⦄ ⊢ V ![a, h] & L = K.ⓑ{I}V.
/2 width=3 by nv_inv_zero_aux/ qed-.

fact nv_inv_lref_aux (a) (h): ∀G,L,X. ⦃G, L⦄ ⊢ X ![a, h] → ∀i. X = #(↑i) →
                              ∃∃I,K. ⦃G, K⦄ ⊢ #i ![a, h] & L = K.ⓘ{I}.
#a #h #G #L #X * -G -L -X
[ #G #L #s #j #H destruct
| #I #G #K #V #_ #j #H destruct
| #I #G #L #i #Hi #j #H destruct /2 width=4 by ex2_2_intro/
| #p #I #G #L #V #T #_ #_ #j #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #j #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #j #H destruct
]
qed-.

lemma nv_inv_lref (a) (h): ∀G,L,i. ⦃G, L⦄ ⊢ #↑i ![a, h] →
                           ∃∃I,K. ⦃G, K⦄ ⊢ #i ![a, h] & L = K.ⓘ{I}.
/2 width=3 by nv_inv_lref_aux/ qed-.

fact nv_inv_gref_aux (a) (h): ∀G,L,X. ⦃G, L⦄ ⊢ X ![a, h] → ∀l. X = §l → ⊥.
#a #h #G #L #X * -G -L -X
[ #G #L #s #l #H destruct
| #I #G #K #V #_ #l #H destruct
| #I #G #K #i #_ #l #H destruct
| #p #I #G #L #V #T #_ #_ #l #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #l #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #l #H destruct
]
qed-.

(* Basic_2A1: uses: snv_inv_gref *)
lemma nv_inv_gref (a) (h): ∀G,L,l. ⦃G, L⦄ ⊢ §l ![a, h] → ⊥.
/2 width=8 by nv_inv_gref_aux/ qed-.

fact nv_inv_bind_aux (a) (h): ∀G,L,X. ⦃G, L⦄ ⊢ X ![a, h] →
                              ∀p,I,V,T. X = ⓑ{p,I}V.T →
                              ∧∧ ⦃G, L⦄ ⊢ V ![a, h]
                               & ⦃G, L.ⓑ{I}V⦄ ⊢ T ![a, h].
#a #h #G #L #X * -G -L -X
[ #G #L #s #q #Z #X1 #X2 #H destruct
| #I #G #K #V #_ #q #Z #X1 #X2 #H destruct
| #I #G #K #i #_ #q #Z #X1 #X2 #H destruct
| #p #I #G #L #V #T #HV #HT #q #Z #X1 #X2 #H destruct /2 width=1 by conj/
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #q #Z #X1 #X2 #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #q #Z #X1 #X2 #H destruct
]
qed-.

(* Basic_2A1: uses: snv_inv_bind *)
lemma nv_inv_bind (a) (h): ∀p,I,G,L,V,T. ⦃G, L⦄ ⊢ ⓑ{p,I}V.T ![a, h] →
                           ∧∧ ⦃G, L⦄ ⊢ V ![a, h]
                            & ⦃G, L.ⓑ{I}V⦄ ⊢ T ![a, h].
/2 width=4 by nv_inv_bind_aux/ qed-.

fact nv_inv_appl_aux (a) (h): ∀G,L,X. ⦃G, L⦄ ⊢ X ![a, h] → ∀V,T. X = ⓐV.T →
                              ∃∃n,p,W0,U0. a = Ⓣ → n = 1 & ⦃G, L⦄ ⊢ V ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                                           ⦃G, L⦄ ⊢ V ➡*[1, h] W0 & ⦃G, L⦄ ⊢ T ➡*[n, h] ⓛ{p}W0.U0.
#a #h #G #L #X * -L -X
[ #G #L #s #X1 #X2 #H destruct
| #I #G #K #V #_ #X1 #X2 #H destruct
| #I #G #K #i #_ #X1 #X2 #H destruct
| #p #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #n #p #G #L #V #W0 #T #U0 #Ha #HV #HT #HVW0 #HTU0 #X1 #X2 #H destruct /3 width=7 by ex5_4_intro/
| #G #L #U #T #U0 #_ #_ #_ #_ #X1 #X2 #H destruct
]
qed-.

(* Basic_2A1: uses: snv_inv_appl *)
lemma nv_inv_appl (a) (h): ∀G,L,V,T. ⦃G, L⦄ ⊢ ⓐV.T ![a, h] →
                           ∃∃n,p,W0,U0. a = Ⓣ → n = 1 & ⦃G, L⦄ ⊢ V ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                                        ⦃G, L⦄ ⊢ V ➡*[1, h] W0 & ⦃G, L⦄ ⊢ T ➡*[n, h] ⓛ{p}W0.U0.
/2 width=3 by nv_inv_appl_aux/ qed-.

fact nv_inv_cast_aux (a) (h): ∀G,L,X. ⦃G, L⦄ ⊢ X ![a, h] → ∀U,T. X = ⓝU.T →
                              ∃∃U0. ⦃G, L⦄ ⊢ U ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                                    ⦃G, L⦄ ⊢ U ➡*[h] U0 & ⦃G, L⦄ ⊢ T ➡*[1, h] U0.
#a #h #G #L #X * -G -L -X
[ #G #L #s #X1 #X2 #H destruct
| #I #G #K #V #_ #X1 #X2 #H destruct
| #I #G #K #i #_ #X1 #X2 #H destruct
| #p #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #X1 #X2 #H destruct
| #G #L #U #T #U0 #HV #HT #HU0 #HTU0 #X1 #X2 #H destruct /2 width=3 by ex4_intro/
]
qed-.

(* Basic_2A1: uses: snv_inv_appl *)
lemma nv_inv_cast (a) (h): ∀G,L,U,T. ⦃G, L⦄ ⊢ ⓝU.T ![a, h] →
                           ∃∃U0. ⦃G, L⦄ ⊢ U ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                                 ⦃G, L⦄ ⊢ U ➡*[h] U0 & ⦃G, L⦄ ⊢ T ➡*[1, h] U0.
/2 width=3 by nv_inv_cast_aux/ qed-.
