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

include "basic_2/notation/relations/nativevalid_4.ma".
include "basic_2/computation/cpds.ma".
include "basic_2/equivalence/cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

inductive snv (h:sh) (g:sd h): lenv → predicate term ≝
| snv_sort: ∀L,k. snv h g L (⋆k)
| snv_lref: ∀I,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → snv h g K V → snv h g L (#i)
| snv_bind: ∀a,I,L,V,T. snv h g L V → snv h g (L.ⓑ{I}V) T → snv h g L (ⓑ{a,I}V.T)
| snv_appl: ∀a,L,V,W,W0,T,U,l. snv h g L V → snv h g L T →
            ⦃G, L⦄ ⊢ V •[h, g] ⦃l+1, W⦄ → ⦃G, L⦄ ⊢ W ➡* W0 →
            ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W0.U → snv h g L (ⓐV.T)
| snv_cast: ∀L,W,T,U,l. snv h g L W → snv h g L T →
            ⦃G, L⦄ ⊢ T •[h, g] ⦃l+1, U⦄ → ⦃G, L⦄ ⊢ U ⬌* W → snv h g L (ⓝW.T)
.

interpretation "stratified native validity (term)"
   'NativeValid h g L T = (snv h g L T).

(* Basic inversion lemmas ***************************************************)

fact snv_inv_lref_aux: ∀h,g,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀i. X = #i →
                       ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V & ⦃h, K⦄ ⊢ V ¡[h, g].
#h #g #L #X * -L -X
[ #L #k #i #H destruct
| #I #L #K #V #i0 #HLK #HV #i #H destruct /2 width=5/
| #a #I #L #V #T #_ #_ #i #H destruct
| #a #L #V #W #W0 #T #U #l #_ #_ #_ #_ #_ #i #H destruct
| #L #W #T #U #l #_ #_ #_ #_ #i #H destruct
]
qed.

lemma snv_inv_lref: ∀h,g,L,i. ⦃G, L⦄ ⊢ #i ¡[h, g] →
                    ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V & ⦃h, K⦄ ⊢ V ¡[h, g].
/2 width=3/ qed-.

fact snv_inv_gref_aux: ∀h,g,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀p. X = §p → ⊥.
#h #g #L #X * -L -X
[ #L #k #p #H destruct
| #I #L #K #V #i #_ #_ #p #H destruct
| #a #I #L #V #T #_ #_ #p #H destruct
| #a #L #V #W #W0 #T #U #l #_ #_ #_ #_ #_ #p #H destruct
| #L #W #T #U #l #_ #_ #_ #_ #p #H destruct
]
qed.

lemma snv_inv_gref: ∀h,g,L,p. ⦃G, L⦄ ⊢ §p ¡[h, g] → ⊥.
/2 width=7/ qed-.

fact snv_inv_bind_aux: ∀h,g,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                       ⦃G, L⦄ ⊢ V ¡[h, g] ∧ ⦃h, L.ⓑ{I}V⦄ ⊢ T ¡[h, g].
#h #g #L #X * -L -X
[ #L #k #a #I #V #T #H destruct
| #I0 #L #K #V0 #i #_ #_ #a #I #V #T #H destruct
| #b #I0 #L #V0 #T0 #HV0 #HT0 #a #I #V #T #H destruct /2 width=1/
| #b #L #V0 #W0 #W00 #T0 #U0 #l #_ #_ #_ #_ #_ #a #I #V #T #H destruct
| #L #W0 #T0 #U0 #l #_ #_ #_ #_ #a #I #V #T #H destruct
]
qed.

lemma snv_inv_bind: ∀h,g,a,I,L,V,T. ⦃G, L⦄ ⊢ ⓑ{a,I}V.T ¡[h, g] →
                        ⦃G, L⦄ ⊢ V ¡[h, g] ∧ ⦃h, L.ⓑ{I}V⦄ ⊢ T ¡[h, g].
/2 width=4/ qed-.

fact snv_inv_appl_aux: ∀h,g,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀V,T. X = ⓐV.T →
                       ∃∃a,W,W0,U,l. ⦃G, L⦄ ⊢ V ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                                   ⦃G, L⦄ ⊢ V •[h, g] ⦃l+1, W⦄ & ⦃G, L⦄ ⊢ W ➡* W0 &
                                   ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W0.U.
#h #g #L #X * -L -X
[ #L #k #V #T #H destruct
| #I #L #K #V0 #i #_ #_ #V #T #H destruct
| #a #I #L #V0 #T0 #_ #_ #V #T #H destruct
| #a #L #V0 #W0 #W00 #T0 #U0 #l #HV0 #HT0 #HVW0 #HW00 #HTU0 #V #T #H destruct /2 width=8/
| #L #W0 #T0 #U0 #l #_ #_ #_ #_ #V #T #H destruct
]
qed.

lemma snv_inv_appl: ∀h,g,L,V,T. ⦃G, L⦄ ⊢ ⓐV.T ¡[h, g] →
                    ∃∃a,W,W0,U,l. ⦃G, L⦄ ⊢ V ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                                ⦃G, L⦄ ⊢ V •[h, g] ⦃l+1, W⦄ & ⦃G, L⦄ ⊢ W ➡* W0 &
                                ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W0.U.
/2 width=3/ qed-.

fact snv_inv_cast_aux: ∀h,g,L,X. ⦃G, L⦄ ⊢ X ¡[h, g] → ∀W,T. X = ⓝW.T →
                       ∃∃U,l. ⦃G, L⦄ ⊢ W ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                              ⦃G, L⦄ ⊢ T •[h, g] ⦃l+1, U⦄ & ⦃G, L⦄ ⊢ U ⬌* W.
#h #g #L #X * -L -X
[ #L #k #W #T #H destruct
| #I #L #K #V #i #_ #_ #W #T #H destruct
| #a #I #L #V #T0 #_ #_ #W #T #H destruct
| #a #L #V #W0 #W00 #T0 #U #l #_ #_ #_ #_ #_ #W #T #H destruct
| #L #W0 #T0 #U0 #l #HW0 #HT0 #HTU0 #HUW0 #W #T #H destruct /2 width=4/
]
qed.

lemma snv_inv_cast: ∀h,g,L,W,T. ⦃G, L⦄ ⊢ ⓝW.T ¡[h, g] →
                    ∃∃U,l. ⦃G, L⦄ ⊢ W ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g] &
                           ⦃G, L⦄ ⊢ T •[h, g] ⦃l+1, U⦄ & ⦃G, L⦄ ⊢ U ⬌* W.
/2 width=3/ qed-.

(* Basic forward lemmas *****************************************************)

lemma snv_fwd_ssta: ∀h,g,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] → ∃∃l,U. ⦃G, L⦄ ⊢ T •[h, g] ⦃l, U⦄.
#h #g #L #T #H elim H -L -T
[ #L #k elim (deg_total h g k) /3 width=3/
| * #L #K #V #i #HLK #_ * #l0 #W #HVW
  [ elim (lift_total W 0 (i+1)) /3 width=8/
  | elim (lift_total V 0 (i+1)) /3 width=8/
  ]
| #a #I #L #V #T #_ #_ #_ * /3 width=3/
| #a #L #V #W #W1 #T0 #T1 #l #_ #_ #_ #_ #_ #_ * /3 width=3/
| #L #W #T #U #l #_ #_ #HTU #_ #_ #_ /3 width=3/ (**) (* auto fails without the last #_ *)
]
qed-.
