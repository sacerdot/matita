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

include "basic_2/computation/cprs.ma".
include "basic_2/computation/xprs.ma".
include "basic_2/equivalence/cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

inductive snv (h:sh) (g:sd h): lenv → predicate term ≝
| snv_sort: ∀L,k. snv h g L (⋆k)
| snv_lref: ∀I,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → snv h g K V → snv h g L (#i)
| snv_bind: ∀I,L,V,T. snv h g L V → snv h g (L.ⓑ{I}V) T → snv h g L (ⓑ{I}V.T)
| snv_appl: ∀L,V,W,W0,T,U,l. snv h g L V → snv h g L T →
            ⦃h, L⦄ ⊢ V •[g, l + 1] W → L ⊢ W ➡* W0 →
            ⦃h, L⦄ ⊢ T ➸*[g] ⓛW0.U → snv h g L (ⓐV.T)
| snv_cast: ∀L,W,T,U,l. snv h g L W → snv h g L T →
            ⦃h, L⦄ ⊢ T •[g, l + 1] U → L ⊢ U ⬌* W → snv h g L (ⓝW.T)
.

interpretation "stratified native validity (term)"
   'NativeValid h g L T = (snv h g L T).

(* Basic inversion lemmas ***************************************************)

lemma snv_inv_bind_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀I,V,T. X = ⓑ{I}V.T →
                        ⦃h, L⦄ ⊩ V :[g] ∧ ⦃h, L.ⓑ{I}V⦄ ⊩ T :[g].
#h #g #L #X * -L -X
[ #L #k #I #V #T #H destruct
| #I0 #L #K #V0 #i #_ #_ #I #V #T #H destruct
| #I0 #L #V0 #T0 #HV0 #HT0 #I #V #T #H destruct /2 width=1/
| #L #V0 #W0 #W00 #T0 #U0 #l #_ #_ #_ #_ #_ #I #V #T #H destruct
| #L #W0 #T0 #U0 #l #_ #_ #_ #_ #I #V #T #H destruct
]
qed.

lemma snv_inv_bind: ∀h,g,I,L,V,T. ⦃h, L⦄ ⊩ ⓑ{I}V.T :[g] →
                        ⦃h, L⦄ ⊩ V :[g] ∧ ⦃h, L.ⓑ{I}V⦄ ⊩ T :[g].
/2 width=3/ qed-.

lemma snv_inv_appl_aux: ∀h,g,L,X. ⦃h, L⦄ ⊩ X :[g] → ∀V,T. X = ⓐV.T →
                        ∃∃W,W0,U,l. ⦃h, L⦄ ⊩ V :[g] & ⦃h, L⦄ ⊩ T :[g] &
                                    ⦃h, L⦄ ⊢ V •[g, l + 1] W & L ⊢ W ➡* W0 &
                                    ⦃h, L⦄ ⊢ T ➸*[g] ⓛW0.U.
#h #g #L #X * -L -X
[ #L #k #V #T #H destruct
| #I #L #K #V0 #i #_ #_ #V #T #H destruct
| #I #L #V0 #T0 #_ #_ #V #T #H destruct
| #L #V0 #W0 #W00 #T0 #U0 #l #HV0 #HT0 #HVW0 #HW00 #HTU0 #V #T #H destruct /2 width=7/
| #L #W0 #T0 #U0 #l #_ #_ #_ #_ #V #T #H destruct
]
qed.

lemma snv_inv_appl: ∀h,g,L,V,T. ⦃h, L⦄ ⊩ ⓐV.T :[g] →
                    ∃∃W,W0,U,l. ⦃h, L⦄ ⊩ V :[g] & ⦃h, L⦄ ⊩ T :[g] &
                                ⦃h, L⦄ ⊢ V •[g, l + 1] W & L ⊢ W ➡* W0 &
                                ⦃h, L⦄ ⊢ T ➸*[g] ⓛW0.U.
/2 width=3/ qed-.
