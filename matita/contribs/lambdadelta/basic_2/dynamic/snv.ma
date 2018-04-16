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
inductive snv (h) (o): relation3 genv lenv term ≝
| snv_sort: ∀G,L,s. snv h o G L (⋆s)
| snv_lref: ∀I,G,L,K,V,i. ⬇[i] L ≘ K.ⓑ{I}V → snv h o G K V → snv h o G L (#i)
| snv_bind: ∀a,I,G,L,V,T. snv h o G L V → snv h o G (L.ⓑ{I}V) T → snv h o G L (ⓑ{a,I}V.T)
| snv_appl: ∀a,G,L,V,W0,T,U0,d. snv h o G L V → snv h o G L T →
            ⦃G, L⦄ ⊢ V •*➡*[h, o, 1] W0 → ⦃G, L⦄ ⊢ T •*➡*[h, o, d] ⓛ{a}W0.U0 → snv h o G L (ⓐV.T)
| snv_cast: ∀G,L,U,T,U0. snv h o G L U → snv h o G L T →
            ⦃G, L⦄ ⊢ U •*➡*[h, o, 0] U0 → ⦃G, L⦄ ⊢ T •*➡*[h, o, 1] U0 → snv h o G L (ⓝU.T)
.

interpretation "stratified native validity (term)"
   'NativeValid h o G L T = (snv h o G L T).

(* Basic inversion lemmas ***************************************************)

fact snv_inv_lref_aux: ∀h,o,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, o] → ∀i. X = #i →
                       ∃∃I,K,V. ⬇[i] L ≘ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ¡[h, o].
#h #o #G #L #X * -G -L -X
[ #G #L #s #i #H destruct
| #I #G #L #K #V #i0 #HLK #HV #i #H destruct /2 width=5 by ex2_3_intro/
| #a #I #G #L #V #T #_ #_ #i #H destruct
| #a #G #L #V #W0 #T #U0 #d #_ #_ #_ #_ #i #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #i #H destruct
]
qed-.

lemma snv_inv_lref: ∀h,o,G,L,i. ⦃G, L⦄ ⊢ #i ¡[h, o] →
                    ∃∃I,K,V. ⬇[i] L ≘ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ¡[h, o].
/2 width=3 by snv_inv_lref_aux/ qed-.

fact snv_inv_gref_aux: ∀h,o,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, o] → ∀p. X = §p → ⊥.
#h #o #G #L #X * -G -L -X
[ #G #L #s #p #H destruct
| #I #G #L #K #V #i #_ #_ #p #H destruct
| #a #I #G #L #V #T #_ #_ #p #H destruct
| #a #G #L #V #W0 #T #U0 #d #_ #_ #_ #_ #p #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #p #H destruct
]
qed-.

lemma snv_inv_gref: ∀h,o,G,L,p. ⦃G, L⦄ ⊢ §p ¡[h, o] → ⊥.
/2 width=8 by snv_inv_gref_aux/ qed-.

fact snv_inv_bind_aux: ∀h,o,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, o] → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                       ⦃G, L⦄ ⊢ V ¡[h, o] ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ T ¡[h, o].
#h #o #G #L #X * -G -L -X
[ #G #L #s #b #Z #X1 #X2 #H destruct
| #I #G #L #K #V #i #_ #_ #b #Z #X1 #X2 #H destruct
| #a #I #G #L #V #T #HV #HT #b #Z #X1 #X2 #H destruct /2 width=1 by conj/
| #a #G #L #V #W0 #T #U0 #d #_ #_ #_ #_ #b #Z #X1 #X2 #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #b #Z #X1 #X2 #H destruct
]
qed-.

lemma snv_inv_bind: ∀h,o,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T ¡[h, o] →
                    ⦃G, L⦄ ⊢ V ¡[h, o] ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ T ¡[h, o].
/2 width=4 by snv_inv_bind_aux/ qed-.

fact snv_inv_appl_aux: ∀h,o,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, o] → ∀V,T. X = ⓐV.T →
                       ∃∃a,W0,U0,d. ⦃G, L⦄ ⊢ V ¡[h, o] & ⦃G, L⦄ ⊢ T ¡[h, o] &
                                    ⦃G, L⦄ ⊢ V •*➡*[h, o, 1] W0 & ⦃G, L⦄ ⊢ T •*➡*[h, o, d] ⓛ{a}W0.U0.
#h #o #G #L #X * -L -X
[ #G #L #s #X1 #X2 #H destruct
| #I #G #L #K #V #i #_ #_ #X1 #X2 #H destruct
| #a #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #a #G #L #V #W0 #T #U0 #d #HV #HT #HVW0 #HTU0 #X1 #X2 #H destruct /2 width=6 by ex4_4_intro/
| #G #L #U #T #U0 #_ #_ #_ #_ #X1 #X2 #H destruct
]
qed-.

lemma snv_inv_appl: ∀h,o,G,L,V,T. ⦃G, L⦄ ⊢ ⓐV.T ¡[h, o] →
                    ∃∃a,W0,U0,d. ⦃G, L⦄ ⊢ V ¡[h, o] & ⦃G, L⦄ ⊢ T ¡[h, o] &
                                 ⦃G, L⦄ ⊢ V •*➡*[h, o, 1] W0 & ⦃G, L⦄ ⊢ T •*➡*[h, o, d] ⓛ{a}W0.U0.
/2 width=3 by snv_inv_appl_aux/ qed-.

fact snv_inv_cast_aux: ∀h,o,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, o] → ∀U,T. X = ⓝU.T →
                       ∃∃U0. ⦃G, L⦄ ⊢ U ¡[h, o] & ⦃G, L⦄ ⊢ T ¡[h, o] &
                             ⦃G, L⦄ ⊢ U •*➡*[h, o, 0] U0 & ⦃G, L⦄ ⊢ T •*➡*[h, o, 1] U0.
#h #o #G #L #X * -G -L -X
[ #G #L #s #X1 #X2 #H destruct
| #I #G #L #K #V #i #_ #_ #X1 #X2 #H destruct
| #a #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #a #G #L #V #W0 #T #U0 #d #_ #_ #_ #_ #X1 #X2 #H destruct
| #G #L #U #T #U0 #HV #HT #HU0 #HTU0 #X1 #X2 #H destruct /2 width=3 by ex4_intro/
]
qed-.

lemma snv_inv_cast: ∀h,o,G,L,U,T. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, o] →
                    ∃∃U0. ⦃G, L⦄ ⊢ U ¡[h, o] & ⦃G, L⦄ ⊢ T ¡[h, o] &
                          ⦃G, L⦄ ⊢ U •*➡*[h, o, 0] U0 & ⦃G, L⦄ ⊢ T •*➡*[h, o, 1] U0.
/2 width=3 by snv_inv_cast_aux/ qed-.
