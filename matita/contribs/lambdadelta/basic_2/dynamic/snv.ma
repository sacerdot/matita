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

include "basic_2/notation/relations/nativevalid_5.ma".
include "basic_2/computation/scpds.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* activate genv *)
inductive snv (h) (g): relation3 genv lenv term ≝
| snv_sort: ∀G,L,k. snv h g G L (⋆k)
| snv_lref: ∀I,G,L,K,V,i. ⇩[i] L ≡ K.ⓑ{I}V → snv h g G K V → snv h g G L (#i)
| snv_bind: ∀a,I,G,L,V,T. snv h g G L V → snv h g G (L.ⓑ{I}V) T → snv h g G L (ⓑ{a,I}V.T)
| snv_appl: ∀a,G,L,V,W0,T,U0,l. snv h g G L V → snv h g G L T →
            ⦃G, L⦄ ⊢ V •*➡*[h, g, 1] W0 → ⦃G, L⦄ ⊢ T •*➡*[h, g, l] ⓛ{a}W0.U0 → snv h g G L (ⓐV.T)
| snv_cast: ∀G,L,U,T,U0. snv h g G L U → snv h g G L T →
            ⦃G, L⦄ ⊢ U ➡* U0 → ⦃G, L⦄ ⊢ T •*➡*[h, g, 1] U0 → snv h g G L (ⓝU.T)
.

interpretation "stratified native validity (term)"
   'NativeValid h g G L T = (snv h g G L T).

(* Basic inversion lemmas ***************************************************)

fact snv_inv_lref_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀i. X = #i →
                       ∃∃I,K,V. ⇩[i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ¡[h, g].
#h #g #G #L #X * -G -L -X
[ #G #L #k #i #H destruct
| #I #G #L #K #V #i0 #HLK #HV #i #H destruct /2 width=5 by ex2_3_intro/
| #a #I #G #L #V #T #_ #_ #i #H destruct
| #a #G #L #V #W0 #T #U0 #l #_ #_ #_ #_ #i #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #i #H destruct
]
qed-.

lemma snv_inv_lref: ∀h,g,G,L,i. ⦃G, L⦄ ⊢ #i ¡[h, g] →
                    ∃∃I,K,V. ⇩[i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ¡[h, g].
/2 width=3 by snv_inv_lref_aux/ qed-.

fact snv_inv_gref_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀p. X = §p → ⊥.
#h #g #G #L #X * -G -L -X
[ #G #L #k #p #H destruct
| #I #G #L #K #V #i #_ #_ #p #H destruct
| #a #I #G #L #V #T #_ #_ #p #H destruct
| #a #G #L #V #W0 #T #U0 #l #_ #_ #_ #_ #p #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #p #H destruct
]
qed-.

lemma snv_inv_gref: ∀h,g,G,L,p. ⦃G, L⦄ ⊢ §p ¡[h, g] → ⊥.
/2 width=8 by snv_inv_gref_aux/ qed-.

fact snv_inv_bind_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                       ⦃G, L⦄ ⊢ V ¡[h, g] ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ T ¡[h, g].
#h #g #G #L #X * -G -L -X
[ #G #L #k #b #Z #X1 #X2 #H destruct
| #I #G #L #K #V #i #_ #_ #b #Z #X1 #X2 #H destruct
| #a #I #G #L #V #T #HV #HT #b #Z #X1 #X2 #H destruct /2 width=1 by conj/
| #a #G #L #V #W0 #T #U0 #l #_ #_ #_ #_ #b #Z #X1 #X2 #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #b #Z #X1 #X2 #H destruct
]
qed-.

lemma snv_inv_bind: ∀h,g,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T ¡[h, g] →
                    ⦃G, L⦄ ⊢ V ¡[h, g] ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ T ¡[h, g].
/2 width=4 by snv_inv_bind_aux/ qed-.

fact snv_inv_appl_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀V,T. X = ⓐV.T →
                       ∃∃a,W0,U0,l. ⦃G, L⦄ ⊢ V ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                                    ⦃G, L⦄ ⊢ V •*➡*[h, g, 1] W0 & ⦃G, L⦄ ⊢ T •*➡*[h, g, l] ⓛ{a}W0.U0.
#h #g #G #L #X * -L -X
[ #G #L #k #X1 #X2 #H destruct
| #I #G #L #K #V #i #_ #_ #X1 #X2 #H destruct
| #a #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #a #G #L #V #W0 #T #U0 #l #HV #HT #HVW0 #HTU0 #X1 #X2 #H destruct /2 width=6 by ex4_4_intro/
| #G #L #U #T #U0 #_ #_ #_ #_ #X1 #X2 #H destruct
]
qed-.

lemma snv_inv_appl: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ⓐV.T ¡[h, g] →
                    ∃∃a,W0,U0,l. ⦃G, L⦄ ⊢ V ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                                 ⦃G, L⦄ ⊢ V •*➡*[h, g, 1] W0 & ⦃G, L⦄ ⊢ T •*➡*[h, g, l] ⓛ{a}W0.U0.
/2 width=3 by snv_inv_appl_aux/ qed-.

fact snv_inv_cast_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀U,T. X = ⓝU.T →
                       ∃∃U0. ⦃G, L⦄ ⊢ U ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                             ⦃G, L⦄ ⊢ U ➡* U0 & ⦃G, L⦄ ⊢ T •*➡*[h, g, 1] U0.
#h #g #G #L #X * -G -L -X
[ #G #L #k #X1 #X2 #H destruct
| #I #G #L #K #V #i #_ #_ #X1 #X2 #H destruct
| #a #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #a #G #L #V #W0 #T #U0 #l #_ #_ #_ #_ #X1 #X2 #H destruct
| #G #L #U #T #U0 #HV #HT #HU0 #HTU0 #X1 #X2 #H destruct /2 width=3 by ex4_intro/
]
qed-.

lemma snv_inv_cast: ∀h,g,G,L,U,T. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g] →
                    ∃∃U0. ⦃G, L⦄ ⊢ U ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                          ⦃G, L⦄ ⊢ U ➡* U0 & ⦃G, L⦄ ⊢ T •*➡*[h, g, 1] U0.
/2 width=3 by snv_inv_cast_aux/ qed-.
