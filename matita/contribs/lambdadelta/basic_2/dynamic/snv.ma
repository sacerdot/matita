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
include "basic_2/computation/cpds.ma".
include "basic_2/equivalence/cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

definition scast: ∀h. sd h → nat → relation4 genv lenv term term ≝
                  λh,g,l,G,L,V,W. ∀V0,W0,l0.
                  l0 ≤ l → ⦃G, L⦄ ⊢ V •*[h, g, l0+1] V0 → ⦃G, L⦄ ⊢ W •*[h, g, l0] W0 → ⦃G, L⦄ ⊢ V0 ⬌* W0.

(* activate genv *)
inductive snv (h:sh) (g:sd h): relation3 genv lenv term ≝
| snv_sort: ∀G,L,k. snv h g G L (⋆k)
| snv_lref: ∀I,G,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → snv h g G K V → snv h g G L (#i)
| snv_bind: ∀a,I,G,L,V,T. snv h g G L V → snv h g G (L.ⓑ{I}V) T → snv h g G L (ⓑ{a,I}V.T)
| snv_appl: ∀a,G,L,V,W,W0,T,U,l. snv h g G L V → snv h g G L T →
            ⦃G, L⦄ ⊢ V ▪[h, g] l+1 → ⦃G, L⦄ ⊢ V •[h, g] W → ⦃G, L⦄ ⊢ W ➡* W0 →
            ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W0.U → snv h g G L (ⓐV.T)
| snv_cast: ∀G,L,W,T,U,l. snv h g G L W → snv h g G L T →
            ⦃G, L⦄ ⊢ T ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T •[h, g] U → ⦃G, L⦄ ⊢ U ⬌* W → snv h g G L (ⓝW.T)
.

interpretation "stratified native validity (term)"
   'NativeValid h g G L T = (snv h g G L T).

(* Basic inversion lemmas ***************************************************)

fact snv_inv_lref_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀i. X = #i →
                       ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ¡[h, g].
#h #g #G #L #X * -G -L -X
[ #G #L #k #i #H destruct
| #I #G #L #K #V #i0 #HLK #HV #i #H destruct /2 width=5/
| #a #I #G #L #V #T #_ #_ #i #H destruct
| #a #G #L #V #W #W0 #T #U #l #_ #_ #_ #_ #_ #_ #i #H destruct
| #G #L #W #T #U #l #_ #_ #_ #_ #_ #i #H destruct
]
qed-.

lemma snv_inv_lref: ∀h,g,G,L,i. ⦃G, L⦄ ⊢ #i ¡[h, g] →
                    ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ¡[h, g].
/2 width=3 by snv_inv_lref_aux/ qed-.

fact snv_inv_gref_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀p. X = §p → ⊥.
#h #g #G #L #X * -G -L -X
[ #G #L #k #p #H destruct
| #I #G #L #K #V #i #_ #_ #p #H destruct
| #a #I #G #L #V #T #_ #_ #p #H destruct
| #a #G #L #V #W #W0 #T #U #l #_ #_ #_ #_ #_ #_ #p #H destruct
| #G #L #W #T #U #l #_ #_ #_ #_ #_ #p #H destruct
]
qed-.

lemma snv_inv_gref: ∀h,g,G,L,p. ⦃G, L⦄ ⊢ §p ¡[h, g] → ⊥.
/2 width=8 by snv_inv_gref_aux/ qed-.

fact snv_inv_bind_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                       ⦃G, L⦄ ⊢ V ¡[h, g] ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ T ¡[h, g].
#h #g #G #L #X * -G -L -X
[ #G #L #k #a #I #V #T #H destruct
| #I0 #G #L #K #V0 #i #_ #_ #a #I #V #T #H destruct
| #b #I0 #G #L #V0 #T0 #HV0 #HT0 #a #I #V #T #H destruct /2 width=1/
| #b #G #L #V0 #W0 #W00 #T0 #U0 #l #_ #_ #_ #_#_ #_ #a #I #V #T #H destruct
| #G #L #W0 #T0 #U0 #l #_ #_ #_ #_ #_ #a #I #V #T #H destruct
]
qed-.

lemma snv_inv_bind: ∀h,g,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T ¡[h, g] →
                    ⦃G, L⦄ ⊢ V ¡[h, g] ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ T ¡[h, g].
/2 width=4 by snv_inv_bind_aux/ qed-.

fact snv_inv_appl_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀V,T. X = ⓐV.T →
                       ∃∃a,W,W0,U,l. ⦃G, L⦄ ⊢ V ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                                     ⦃G, L⦄ ⊢ V ▪[h, g] l+1 & ⦃G, L⦄ ⊢ V •[h, g] W & ⦃G, L⦄ ⊢ W ➡* W0 &
                                     ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W0.U.
#h #g #G #L #X * -L -X
[ #G #L #k #V #T #H destruct
| #I #G #L #K #V0 #i #_ #_ #V #T #H destruct
| #a #I #G #L #V0 #T0 #_ #_ #V #T #H destruct
| #a #G #L #V0 #W0 #W00 #T0 #U0 #l #HV0 #HT0 #Hl #HVW0 #HW00 #HTU0 #V #T #H destruct /2 width=8/
| #G #L #W0 #T0 #U0 #l #_ #_ #_ #_ #_ #V #T #H destruct
]
qed-.

lemma snv_inv_appl: ∀h,g,G,L,V,T. ⦃G, L⦄ ⊢ ⓐV.T ¡[h, g] →
                    ∃∃a,W,W0,U,l. ⦃G, L⦄ ⊢ V ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                                  ⦃G, L⦄ ⊢ V ▪[h, g] l+1 & ⦃G, L⦄ ⊢ V •[h, g] W & ⦃G, L⦄ ⊢ W ➡* W0 &
                                  ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W0.U.
/2 width=3 by snv_inv_appl_aux/ qed-.

fact snv_inv_cast_aux: ∀h,g,G,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀W,T. X = ⓝW.T →
                       ∃∃U,l. ⦃G, L⦄ ⊢ W ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                              ⦃G, L⦄ ⊢ T ▪[h, g] l+1 & ⦃G, L⦄ ⊢ T •[h, g] U & ⦃G, L⦄ ⊢ U ⬌* W.
#h #g #G #L #X * -G -L -X
[ #G #L #k #W #T #H destruct
| #I #G #L #K #V #i #_ #_ #W #T #H destruct
| #a #I #G #L #V #T0 #_ #_ #W #T #H destruct
| #a #G #L #V #W0 #W00 #T0 #U #l #_ #_ #_ #_ #_ #_ #W #T #H destruct
| #G #L #W0 #T0 #U0 #l #HW0 #HT0 #Hl #HTU0 #HUW0 #W #T #H destruct /2 width=4/
]
qed-.

lemma snv_inv_cast: ∀h,g,G,L,W,T. ⦃G, L⦄ ⊢ ⓝW.T ¡[h, g] →
                    ∃∃U,l. ⦃G, L⦄ ⊢ W ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                           ⦃G, L⦄ ⊢ T ▪[h, g] l+1 & ⦃G, L⦄ ⊢ T •[h, g] U & ⦃G, L⦄ ⊢ U ⬌* W.
/2 width=3 by snv_inv_cast_aux/ qed-.
