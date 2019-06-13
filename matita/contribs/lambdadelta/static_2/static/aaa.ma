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

include "static_2/notation/relations/atomicarity_4.ma".
include "static_2/syntax/aarity.ma".
include "static_2/syntax/lenv.ma".
include "static_2/syntax/genv.ma".

(* ATONIC ARITY ASSIGNMENT FOR TERMS ****************************************)

(* activate genv *)
inductive aaa: relation4 genv lenv term aarity ≝
| aaa_sort: ∀G,L,s. aaa G L (⋆s) (⓪)
| aaa_zero: ∀I,G,L,V,B. aaa G L V B → aaa G (L.ⓑ{I}V) (#0) B
| aaa_lref: ∀I,G,L,A,i. aaa G L (#i) A → aaa G (L.ⓘ{I}) (#↑i) A
| aaa_abbr: ∀p,G,L,V,T,B,A.
            aaa G L V B → aaa G (L.ⓓV) T A → aaa G L (ⓓ{p}V.T) A
| aaa_abst: ∀p,G,L,V,T,B,A.
            aaa G L V B → aaa G (L.ⓛV) T A → aaa G L (ⓛ{p}V.T) (②B.A)
| aaa_appl: ∀G,L,V,T,B,A. aaa G L V B → aaa G L T (②B.A) → aaa G L (ⓐV.T) A
| aaa_cast: ∀G,L,V,T,A. aaa G L V A → aaa G L T A → aaa G L (ⓝV.T) A
.

interpretation "atomic arity assignment (term)"
   'AtomicArity G L T A = (aaa G L T A).

(* Basic inversion lemmas ***************************************************)

fact aaa_inv_sort_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀s. T = ⋆s → A = ⓪.
#G #L #T #A * -G -L -T -A //
[ #I #G #L #V #B #_ #s #H destruct
| #I #G #L #A #i #_ #s #H destruct
| #p #G #L #V #T #B #A #_ #_ #s #H destruct
| #p #G #L #V #T #B #A #_ #_ #s #H destruct
| #G #L #V #T #B #A #_ #_ #s #H destruct
| #G #L #V #T #A #_ #_ #s #H destruct
]
qed-.

lemma aaa_inv_sort: ∀G,L,A,s. ⦃G,L⦄ ⊢ ⋆s ⁝ A → A = ⓪.
/2 width=6 by aaa_inv_sort_aux/ qed-.

fact aaa_inv_zero_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → T = #0 →
                       ∃∃I,K,V. L = K.ⓑ{I}V & ⦃G,K⦄ ⊢ V ⁝ A.
#G #L #T #A * -G -L -T -A /2 width=5 by ex2_3_intro/
[ #G #L #s #H destruct
| #I #G #L #A #i #_ #H destruct
| #p #G #L #V #T #B #A #_ #_ #H destruct
| #p #G #L #V #T #B #A #_ #_ #H destruct
| #G #L #V #T #B #A #_ #_ #H destruct
| #G #L #V #T #A #_ #_ #H destruct
]
qed-.

lemma aaa_inv_zero: ∀G,L,A. ⦃G,L⦄ ⊢ #0 ⁝ A →
                    ∃∃I,K,V. L = K.ⓑ{I}V & ⦃G,K⦄ ⊢ V ⁝ A.
/2 width=3 by aaa_inv_zero_aux/ qed-.

fact aaa_inv_lref_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀i. T = #(↑i) →
                       ∃∃I,K. L = K.ⓘ{I} & ⦃G,K⦄ ⊢ #i ⁝ A.
#G #L #T #A * -G -L -T -A
[ #G #L #s #j #H destruct
| #I #G #L #V #B #_ #j #H destruct
| #I #G #L #A #i #HA #j #H destruct /2 width=4 by ex2_2_intro/
| #p #G #L #V #T #B #A #_ #_ #j #H destruct
| #p #G #L #V #T #B #A #_ #_ #j #H destruct
| #G #L #V #T #B #A #_ #_ #j #H destruct
| #G #L #V #T #A #_ #_ #j #H destruct
]
qed-.

lemma aaa_inv_lref: ∀G,L,A,i. ⦃G,L⦄ ⊢ #↑i ⁝ A →
                    ∃∃I,K. L = K.ⓘ{I} & ⦃G,K⦄ ⊢ #i ⁝ A.
/2 width=3 by aaa_inv_lref_aux/ qed-.

fact aaa_inv_gref_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀l. T = §l → ⊥.
#G #L #T #A * -G -L -T -A
[ #G #L #s #k #H destruct
| #I #G #L #V #B #_ #k #H destruct
| #I #G #L #A #i #_ #k #H destruct
| #p #G #L #V #T #B #A #_ #_ #k #H destruct
| #p #G #L #V #T #B #A #_ #_ #k #H destruct
| #G #L #V #T #B #A #_ #_ #k #H destruct
| #G #L #V #T #A #_ #_ #k #H destruct
]
qed-.

lemma aaa_inv_gref: ∀G,L,A,l. ⦃G,L⦄ ⊢ §l ⁝ A → ⊥.
/2 width=7 by aaa_inv_gref_aux/ qed-.

fact aaa_inv_abbr_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀p,W,U. T = ⓓ{p}W.U →
                       ∃∃B. ⦃G,L⦄ ⊢ W ⁝ B & ⦃G,L.ⓓW⦄ ⊢ U ⁝ A.
#G #L #T #A * -G -L -T -A
[ #G #L #s #q #W #U #H destruct
| #I #G #L #V #B #_ #q #W #U #H destruct
| #I #G #L #A #i #_ #q #W #U #H destruct
| #p #G #L #V #T #B #A #HV #HT #q #W #U #H destruct /2 width=2 by ex2_intro/
| #p #G #L #V #T #B #A #_ #_ #q #W #U #H destruct
| #G #L #V #T #B #A #_ #_ #q #W #U #H destruct
| #G #L #V #T #A #_ #_ #q #W #U #H destruct
]
qed-.

lemma aaa_inv_abbr: ∀p,G,L,V,T,A. ⦃G,L⦄ ⊢ ⓓ{p}V.T ⁝ A →
                    ∃∃B. ⦃G,L⦄ ⊢ V ⁝ B & ⦃G,L.ⓓV⦄ ⊢ T ⁝ A.
/2 width=4 by aaa_inv_abbr_aux/ qed-.

fact aaa_inv_abst_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀p,W,U. T = ⓛ{p}W.U →
                       ∃∃B1,B2. ⦃G,L⦄ ⊢ W ⁝ B1 & ⦃G,L.ⓛW⦄ ⊢ U ⁝ B2 & A = ②B1.B2.
#G #L #T #A * -G -L -T -A
[ #G #L #s #q #W #U #H destruct
| #I #G #L #V #B #_ #q #W #U #H destruct
| #I #G #L #A #i #_ #q #W #U #H destruct
| #p #G #L #V #T #B #A #_ #_ #q #W #U #H destruct
| #p #G #L #V #T #B #A #HV #HT #q #W #U #H destruct /2 width=5 by ex3_2_intro/
| #G #L #V #T #B #A #_ #_ #q #W #U #H destruct
| #G #L #V #T #A #_ #_ #q #W #U #H destruct
]
qed-.

lemma aaa_inv_abst: ∀p,G,L,W,T,A. ⦃G,L⦄ ⊢ ⓛ{p}W.T ⁝ A →
                    ∃∃B1,B2. ⦃G,L⦄ ⊢ W ⁝ B1 & ⦃G,L.ⓛW⦄ ⊢ T ⁝ B2 & A = ②B1.B2.
/2 width=4 by aaa_inv_abst_aux/ qed-.

fact aaa_inv_appl_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀W,U. T = ⓐW.U →
                       ∃∃B. ⦃G,L⦄ ⊢ W ⁝ B & ⦃G,L⦄ ⊢ U ⁝ ②B.A.
#G #L #T #A * -G -L -T -A
[ #G #L #s #W #U #H destruct
| #I #G #L #V #B #_ #W #U #H destruct
| #I #G #L #A #i #_ #W #U #H destruct
| #p #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #p #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #G #L #V #T #B #A #HV #HT #W #U #H destruct /2 width=3 by ex2_intro/
| #G #L #V #T #A #_ #_ #W #U #H destruct
]
qed-.

lemma aaa_inv_appl: ∀G,L,V,T,A. ⦃G,L⦄ ⊢ ⓐV.T ⁝ A →
                    ∃∃B. ⦃G,L⦄ ⊢ V ⁝ B & ⦃G,L⦄ ⊢ T ⁝ ②B.A.
/2 width=3 by aaa_inv_appl_aux/ qed-.

fact aaa_inv_cast_aux: ∀G,L,T,A. ⦃G,L⦄ ⊢ T ⁝ A → ∀W,U. T = ⓝW.U →
                       ⦃G,L⦄ ⊢ W ⁝ A ∧ ⦃G,L⦄ ⊢ U ⁝ A.
#G #L #T #A * -G -L -T -A
[ #G #L #s #W #U #H destruct
| #I #G #L #V #B #_ #W #U #H destruct
| #I #G #L #A #i #_ #W #U #H destruct
| #p #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #p #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #G #L #V #T #A #HV #HT #W #U #H destruct /2 width=1 by conj/
]
qed-.

lemma aaa_inv_cast: ∀G,L,W,T,A. ⦃G,L⦄ ⊢ ⓝW.T ⁝ A →
                    ⦃G,L⦄ ⊢ W ⁝ A ∧ ⦃G,L⦄ ⊢ T ⁝ A.
/2 width=3 by aaa_inv_cast_aux/ qed-.
