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

include "basic_2/computation/dxprs.ma".
include "basic_2/equivalence/cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

inductive snv (h:sh) (g:sd h): lenv → predicate term ≝
| snv_sort: ∀L,k. snv h g L (⋆k)
| snv_lref: ∀I,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → snv h g K V → snv h g L (#i)
| snv_bind: ∀a,I,L,V,T. snv h g L V → snv h g (L.ⓑ{I}V) T → snv h g L (ⓑ{a,I}V.T)
| snv_appl: ∀a,L,V,W,W0,T,U,l. snv h g L V → snv h g L T →
            ⦃h, L⦄ ⊢ V •[g, l + 1] W → L ⊢ W ➡* W0 →
            ⦃h, L⦄ ⊢ T •*➡*[g] ⓛ{a}W0.U → snv h g L (ⓐV.T)
| snv_cast: ∀L,W,T,U,l. snv h g L W → snv h g L T →
            ⦃h, L⦄ ⊢ T •[g, l + 1] U → L ⊢ U ⬌* W → snv h g L (ⓝW.T)
.

interpretation "stratified native validity (term)"
   'NativeValid h g L T = (snv h g L T).

(* Basic inversion lemmas ***************************************************)

fact snv_inv_lref_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀i. X = #i →
                       ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V & ⦃h, K⦄ ⊩ V :[g].
#h #g #L #X * -L -X
[ #L #k #i #H destruct
| #I #L #K #V #i0 #HLK #HV #i #H destruct /2 width=5/
| #a #I #L #V #T #_ #_ #i #H destruct
| #a #L #V #W #W0 #T #U #l #_ #_ #_ #_ #_ #i #H destruct
| #L #W #T #U #l #_ #_ #_ #_ #i #H destruct
]
qed.

lemma snv_inv_lref: ∀h,g,L,i. ⦃h, L⦄ ⊩ #i :[g] →
                    ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V & ⦃h, K⦄ ⊩ V :[g].
/2 width=3/ qed-.

fact snv_inv_gref_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀p. X = §p → ⊥.
#h #g #L #X * -L -X
[ #L #k #p #H destruct
| #I #L #K #V #i #_ #_ #p #H destruct
| #a #I #L #V #T #_ #_ #p #H destruct
| #a #L #V #W #W0 #T #U #l #_ #_ #_ #_ #_ #p #H destruct
| #L #W #T #U #l #_ #_ #_ #_ #p #H destruct
]
qed.

lemma snv_inv_gref: ∀h,g,L,p. ⦃h, L⦄ ⊩ §p :[g] → ⊥.
/2 width=7/ qed-.

fact snv_inv_bind_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                       ⦃h, L⦄ ⊩ V :[g] ∧ ⦃h, L.ⓑ{I}V⦄ ⊩ T :[g].
#h #g #L #X * -L -X
[ #L #k #a #I #V #T #H destruct
| #I0 #L #K #V0 #i #_ #_ #a #I #V #T #H destruct
| #b #I0 #L #V0 #T0 #HV0 #HT0 #a #I #V #T #H destruct /2 width=1/
| #b #L #V0 #W0 #W00 #T0 #U0 #l #_ #_ #_ #_ #_ #a #I #V #T #H destruct
| #L #W0 #T0 #U0 #l #_ #_ #_ #_ #a #I #V #T #H destruct
]
qed.

lemma snv_inv_bind: ∀h,g,a,I,L,V,T. ⦃h, L⦄ ⊩ ⓑ{a,I}V.T :[g] →
                        ⦃h, L⦄ ⊩ V :[g] ∧ ⦃h, L.ⓑ{I}V⦄ ⊩ T :[g].
/2 width=4/ qed-.

fact snv_inv_appl_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀V,T. X = ⓐV.T →
                       ∃∃a,W,W0,U,l. ⦃h, L⦄ ⊩ V :[g] & ⦃h, L⦄ ⊩ T :[g] &
                                   ⦃h, L⦄ ⊢ V •[g, l + 1] W & L ⊢ W ➡* W0 &
                                   ⦃h, L⦄ ⊢ T •*➡*[g] ⓛ{a}W0.U.
#h #g #L #X * -L -X
[ #L #k #V #T #H destruct
| #I #L #K #V0 #i #_ #_ #V #T #H destruct
| #a #I #L #V0 #T0 #_ #_ #V #T #H destruct
| #a #L #V0 #W0 #W00 #T0 #U0 #l #HV0 #HT0 #HVW0 #HW00 #HTU0 #V #T #H destruct /2 width=8/
| #L #W0 #T0 #U0 #l #_ #_ #_ #_ #V #T #H destruct
]
qed.

lemma snv_inv_appl: ∀h,g,L,V,T. ⦃h, L⦄ ⊩ ⓐV.T :[g] →
                    ∃∃a,W,W0,U,l. ⦃h, L⦄ ⊩ V :[g] & ⦃h, L⦄ ⊩ T :[g] &
                                ⦃h, L⦄ ⊢ V •[g, l + 1] W & L ⊢ W ➡* W0 &
                                ⦃h, L⦄ ⊢ T •*➡*[g] ⓛ{a}W0.U.
/2 width=3/ qed-.

fact snv_inv_cast_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀W,T. X = ⓝW.T →
                       ∃∃U,l. ⦃h, L⦄ ⊩ W :[g] & ⦃h, L⦄ ⊩ T :[g] & 
                              ⦃h, L⦄ ⊢ T •[g, l + 1] U & L ⊢ U ⬌* W.
#h #g #L #X * -L -X
[ #L #k #W #T #H destruct
| #I #L #K #V #i #_ #_ #W #T #H destruct
| #a #I #L #V #T0 #_ #_ #W #T #H destruct
| #a #L #V #W0 #W00 #T0 #U #l #_ #_ #_ #_ #_ #W #T #H destruct
| #L #W0 #T0 #U0 #l #HW0 #HT0 #HTU0 #HUW0 #W #T #H destruct /2 width=4/
]
qed.

lemma snv_inv_cast: ∀h,g,L,W,T. ⦃h, L⦄ ⊩ ⓝW.T :[g] →
                    ∃∃U,l. ⦃h, L⦄ ⊩ W :[g] & ⦃h, L⦄ ⊩ T :[g] &
                           ⦃h, L⦄ ⊢ T •[g, l + 1] U & L ⊢ U ⬌* W.
/2 width=3/ qed-.
