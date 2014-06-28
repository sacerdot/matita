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

include "basic_2/notation/relations/atomicarity_4.ma".
include "basic_2/grammar/aarity.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/substitution/drop.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* activate genv *)
inductive aaa: relation4 genv lenv term aarity ≝
| aaa_sort: ∀G,L,k. aaa G L (⋆k) (⓪)
| aaa_lref: ∀I,G,L,K,V,B,i. ⇩[i] L ≡ K. ⓑ{I}V → aaa G K V B → aaa G L (#i) B
| aaa_abbr: ∀a,G,L,V,T,B,A.
            aaa G L V B → aaa G (L.ⓓV) T A → aaa G L (ⓓ{a}V.T) A
| aaa_abst: ∀a,G,L,V,T,B,A.
            aaa G L V B → aaa G (L.ⓛV) T A → aaa G L (ⓛ{a}V.T) (②B.A)
| aaa_appl: ∀G,L,V,T,B,A. aaa G L V B → aaa G L T (②B.A) → aaa G L (ⓐV.T) A
| aaa_cast: ∀G,L,V,T,A. aaa G L V A → aaa G L T A → aaa G L (ⓝV.T) A
.

interpretation "atomic arity assignment (term)"
   'AtomicArity G L T A = (aaa G L T A).

(* Basic inversion lemmas ***************************************************)

fact aaa_inv_sort_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀k. T = ⋆k → A = ⓪.
#G #L #T #A * -G -L -T -A
[ //
| #I #G #L #K #V #B #i #_ #_ #k #H destruct
| #a #G #L #V #T #B #A #_ #_ #k #H destruct
| #a #G #L #V #T #B #A #_ #_ #k #H destruct
| #G #L #V #T #B #A #_ #_ #k #H destruct
| #G #L #V #T #A #_ #_ #k #H destruct
]
qed-.

lemma aaa_inv_sort: ∀G,L,A,k. ⦃G, L⦄ ⊢ ⋆k ⁝ A → A = ⓪.
/2 width=6 by aaa_inv_sort_aux/ qed-.

fact aaa_inv_lref_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀i. T = #i →
                       ∃∃I,K,V. ⇩[i] L ≡ K.ⓑ{I} V & ⦃G, K⦄ ⊢ V ⁝ A.
#G #L #T #A * -G -L -T -A
[ #G #L #k #i #H destruct
| #I #G #L #K #V #B #j #HLK #HB #i #H destruct /2 width=5 by ex2_3_intro/
| #a #G #L #V #T #B #A #_ #_ #i #H destruct
| #a #G #L #V #T #B #A #_ #_ #i #H destruct
| #G #L #V #T #B #A #_ #_ #i #H destruct
| #G #L #V #T #A #_ #_ #i #H destruct
]
qed-.

lemma aaa_inv_lref: ∀G,L,A,i. ⦃G, L⦄ ⊢ #i ⁝ A →
                    ∃∃I,K,V. ⇩[i] L ≡ K. ⓑ{I} V & ⦃G, K⦄ ⊢ V ⁝ A.
/2 width=3 by aaa_inv_lref_aux/ qed-.

fact aaa_inv_gref_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀p. T = §p → ⊥.
#G #L #T #A * -G -L -T -A
[ #G #L #k #q #H destruct
| #I #G #L #K #V #B #i #HLK #HB #q #H destruct
| #a #G #L #V #T #B #A #_ #_ #q #H destruct
| #a #G #L #V #T #B #A #_ #_ #q #H destruct
| #G #L #V #T #B #A #_ #_ #q #H destruct
| #G #L #V #T #A #_ #_ #q #H destruct
]
qed-.

lemma aaa_inv_gref: ∀G,L,A,p. ⦃G, L⦄ ⊢ §p ⁝ A → ⊥.
/2 width=7 by aaa_inv_gref_aux/ qed-.

fact aaa_inv_abbr_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀a,W,U. T = ⓓ{a}W. U →
                       ∃∃B. ⦃G, L⦄ ⊢ W ⁝ B & ⦃G, L.ⓓW⦄ ⊢ U ⁝ A.
#G #L #T #A * -G -L -T -A
[ #G #L #k #a #W #U #H destruct
| #I #G #L #K #V #B #i #_ #_ #a #W #U #H destruct
| #b #G #L #V #T #B #A #HV #HT #a #W #U #H destruct /2 width=2 by ex2_intro/
| #b #G #L #V #T #B #A #_ #_ #a #W #U #H destruct
| #G #L #V #T #B #A #_ #_ #a #W #U #H destruct
| #G #L #V #T #A #_ #_ #a #W #U #H destruct
]
qed-.

lemma aaa_inv_abbr: ∀a,G,L,V,T,A. ⦃G, L⦄ ⊢ ⓓ{a}V. T ⁝ A →
                    ∃∃B. ⦃G, L⦄ ⊢ V ⁝ B & ⦃G, L.ⓓV⦄ ⊢ T ⁝ A.
/2 width=4 by aaa_inv_abbr_aux/ qed-.

fact aaa_inv_abst_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀a,W,U. T = ⓛ{a}W. U →
                       ∃∃B1,B2. ⦃G, L⦄ ⊢ W ⁝ B1 & ⦃G, L.ⓛW⦄ ⊢ U ⁝ B2 & A = ②B1.B2.
#G #L #T #A * -G -L -T -A
[ #G #L #k #a #W #U #H destruct
| #I #G #L #K #V #B #i #_ #_ #a #W #U #H destruct
| #b #G #L #V #T #B #A #_ #_ #a #W #U #H destruct
| #b #G #L #V #T #B #A #HV #HT #a #W #U #H destruct /2 width=5 by ex3_2_intro/
| #G #L #V #T #B #A #_ #_ #a #W #U #H destruct
| #G #L #V #T #A #_ #_ #a #W #U #H destruct
]
qed-.

lemma aaa_inv_abst: ∀a,G,L,W,T,A. ⦃G, L⦄ ⊢ ⓛ{a}W. T ⁝ A →
                    ∃∃B1,B2. ⦃G, L⦄ ⊢ W ⁝ B1 & ⦃G, L.ⓛW⦄ ⊢ T ⁝ B2 & A = ②B1.B2.
/2 width=4 by aaa_inv_abst_aux/ qed-.

fact aaa_inv_appl_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀W,U. T = ⓐW.U →
                       ∃∃B. ⦃G, L⦄ ⊢ W ⁝ B & ⦃G, L⦄ ⊢ U ⁝ ②B.A.
#G #L #T #A * -G -L -T -A
[ #G #L #k #W #U #H destruct
| #I #G #L #K #V #B #i #_ #_ #W #U #H destruct
| #a #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #a #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #G #L #V #T #B #A #HV #HT #W #U #H destruct /2 width=3 by ex2_intro/
| #G #L #V #T #A #_ #_ #W #U #H destruct
]
qed-.

lemma aaa_inv_appl: ∀G,L,V,T,A. ⦃G, L⦄ ⊢ ⓐV.T ⁝ A →
                    ∃∃B. ⦃G, L⦄ ⊢ V ⁝ B & ⦃G, L⦄ ⊢ T ⁝ ②B.A.
/2 width=3 by aaa_inv_appl_aux/ qed-.

fact aaa_inv_cast_aux: ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∀W,U. T = ⓝW. U →
                       ⦃G, L⦄ ⊢ W ⁝ A ∧ ⦃G, L⦄ ⊢ U ⁝ A.
#G #L #T #A * -G -L -T -A
[ #G #L #k #W #U #H destruct
| #I #G #L #K #V #B #i #_ #_ #W #U #H destruct
| #a #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #a #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #G #L #V #T #B #A #_ #_ #W #U #H destruct
| #G #L #V #T #A #HV #HT #W #U #H destruct /2 width=1 by conj/
]
qed-.

lemma aaa_inv_cast: ∀G,L,W,T,A. ⦃G, L⦄ ⊢ ⓝW. T ⁝ A →
                    ⦃G, L⦄ ⊢ W ⁝ A ∧ ⦃G, L⦄ ⊢ T ⁝ A.
/2 width=3 by aaa_inv_cast_aux/ qed-.
