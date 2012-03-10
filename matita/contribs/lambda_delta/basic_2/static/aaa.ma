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

include "basic_2/grammar/aarity.ma".
include "basic_2/substitution/ldrop.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

inductive aaa: lenv → term → predicate aarity ≝
| aaa_sort: ∀L,k. aaa L (⋆k) ⓪
| aaa_lref: ∀I,L,K,V,B,i. ⇩[0, i] L ≡ K. ⓑ{I} V → aaa K V B → aaa L (#i) B
| aaa_abbr: ∀L,V,T,B,A.
            aaa L V B → aaa (L. ⓓV) T A → aaa L (ⓓV. T) A
| aaa_abst: ∀L,V,T,B,A.
            aaa L V B → aaa (L. ⓛV) T A → aaa L (ⓛV. T) (②B. A)
| aaa_appl: ∀L,V,T,B,A. aaa L V B → aaa L T (②B. A) → aaa L (ⓐV. T) A
| aaa_cast: ∀L,V,T,A. aaa L V A → aaa L T A → aaa L (ⓣV. T) A
.

interpretation "atomic arity assignment (term)"
   'AtomicArity L T A = (aaa L T A).

(* Basic inversion lemmas ***************************************************)

fact aaa_inv_sort_aux: ∀L,T,A. L ⊢ T ÷ A → ∀k. T = ⋆k → A = ⓪.
#L #T #A * -L -T -A
[ //
| #I #L #K #V #B #i #_ #_ #k #H destruct
| #L #V #T #B #A #_ #_ #k #H destruct
| #L #V #T #B #A #_ #_ #k #H destruct
| #L #V #T #B #A #_ #_ #k #H destruct
| #L #V #T #A #_ #_ #k #H destruct
]
qed.

lemma aaa_inv_sort: ∀L,A,k. L ⊢ ⋆k ÷ A → A = ⓪.
/2 width=5/ qed-.

fact aaa_inv_lref_aux: ∀L,T,A. L ⊢ T ÷ A → ∀i. T = #i →
                       ∃∃I,K,V. ⇩[0, i] L ≡ K. ⓑ{I} V & K ⊢ V ÷ A.
#L #T #A * -L -T -A
[ #L #k #i #H destruct
| #I #L #K #V #B #j #HLK #HB #i #H destruct /2 width=5/
| #L #V #T #B #A #_ #_ #i #H destruct
| #L #V #T #B #A #_ #_ #i #H destruct
| #L #V #T #B #A #_ #_ #i #H destruct
| #L #V #T #A #_ #_ #i #H destruct
]
qed.

lemma aaa_inv_lref: ∀L,A,i. L ⊢ #i ÷ A →
                    ∃∃I,K,V. ⇩[0, i] L ≡ K. ⓑ{I} V & K ⊢ V ÷ A.
/2 width=3/ qed-.

fact aaa_inv_abbr_aux: ∀L,T,A. L ⊢ T ÷ A → ∀W,U. T = ⓓW. U →
                       ∃∃B. L ⊢ W ÷ B & L. ⓓW ⊢ U ÷ A.
#L #T #A * -L -T -A
[ #L #k #W #U #H destruct
| #I #L #K #V #B #i #_ #_ #W #U #H destruct
| #L #V #T #B #A #HV #HT #W #U #H destruct /2 width=2/
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #A #_ #_ #W #U #H destruct
]
qed.

lemma aaa_inv_abbr: ∀L,V,T,A. L ⊢ ⓓV. T ÷ A →
                    ∃∃B. L ⊢ V ÷ B & L. ⓓV ⊢ T ÷ A.
/2 width=3/ qed-.

fact aaa_inv_abst_aux: ∀L,T,A. L ⊢ T ÷ A → ∀W,U. T = ⓛW. U →
                       ∃∃B1,B2. L ⊢ W ÷ B1 & L. ⓛW ⊢ U ÷ B2 & A = ②B1. B2.
#L #T #A * -L -T -A
[ #L #k #W #U #H destruct
| #I #L #K #V #B #i #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #B #A #HV #HT #W #U #H destruct /2 width=5/
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #A #_ #_ #W #U #H destruct
]
qed.

lemma aaa_inv_abst: ∀L,W,T,A. L ⊢ ⓛW. T ÷ A →
                    ∃∃B1,B2. L ⊢ W ÷ B1 & L. ⓛW ⊢ T ÷ B2 & A = ②B1. B2.
/2 width=3/ qed-.

fact aaa_inv_appl_aux: ∀L,T,A. L ⊢ T ÷ A → ∀W,U. T = ⓐW. U →
                       ∃∃B. L ⊢ W ÷ B & L ⊢ U ÷ ②B. A.
#L #T #A * -L -T -A
[ #L #k #W #U #H destruct
| #I #L #K #V #B #i #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #B #A #HV #HT #W #U #H destruct /2 width=3/
| #L #V #T #A #_ #_ #W #U #H destruct
]
qed.

lemma aaa_inv_appl: ∀L,V,T,A. L ⊢ ⓐV. T ÷ A →
                    ∃∃B. L ⊢ V ÷ B & L ⊢ T ÷ ②B. A.
/2 width=3/ qed-.

fact aaa_inv_cast_aux: ∀L,T,A. L ⊢ T ÷ A → ∀W,U. T = ⓣW. U →
                       L ⊢ W ÷ A ∧ L ⊢ U ÷ A.
#L #T #A * -L -T -A
[ #L #k #W #U #H destruct
| #I #L #K #V #B #i #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #B #A #_ #_ #W #U #H destruct
| #L #V #T #A #HV #HT #W #U #H destruct /2 width=1/
]
qed.

lemma aaa_inv_cast: ∀L,W,T,A. L ⊢ ⓣW. T ÷ A →
                    L ⊢ W ÷ A ∧ L ⊢ T ÷ A.
/2 width=3/ qed-.
