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

include "basic_2/notation/relations/lazyeqalt_4.ma".
include "basic_2/substitution/lleq_lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Note: alternative definition of lleq *)
inductive lleqa: relation4 ynat term lenv lenv ≝
| lleqa_sort: ∀L1,L2,d,k. |L1| = |L2| → lleqa d (⋆k) L1 L2
| lleqa_skip: ∀L1,L2,d,i. |L1| = |L2| → yinj i < d → lleqa d (#i) L1 L2
| lleqa_lref: ∀I1,I2,L1,L2,K1,K2,V,d,i. d ≤ yinj i →
              ⇩[i] L1 ≡ K1.ⓑ{I1}V → ⇩[i] L2 ≡ K2.ⓑ{I2}V →
              lleqa (yinj 0) V K1 K2 → lleqa d (#i) L1 L2
| lleqa_free: ∀L1,L2,d,i. |L1| = |L2| → |L1| ≤ i → |L2| ≤ i → lleqa d (#i) L1 L2
| lleqa_gref: ∀L1,L2,d,p. |L1| = |L2| → lleqa d (§p) L1 L2
| lleqa_bind: ∀a,I,L1,L2,V,T,d.
              lleqa d V L1 L2 → lleqa (⫯d) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) →
              lleqa d (ⓑ{a,I}V.T) L1 L2
| lleqa_flat: ∀I,L1,L2,V,T,d.
              lleqa d V L1 L2 → lleqa d T L1 L2 → lleqa d (ⓕ{I}V.T) L1 L2
.

interpretation
   "lazy equivalence (local environment) alternative"
   'LazyEqAlt T d L1 L2 = (lleqa d T L1 L2).

(* Main inversion lemmas ****************************************************)

theorem lleqa_inv_lleq: ∀L1,L2,T,d. L1 ⋕⋕[T, d] L2 → L1 ⋕[T, d] L2.
#L1 #L2 #T #d #H elim H -L1 -L2 -T -d
/2 width=8 by lleq_flat, lleq_bind, lleq_gref, lleq_free, lleq_lref, lleq_skip, lleq_sort/
qed-.

(* Main properties **********************************************************)

theorem lleq_lleqa: ∀L1,T,L2,d. L1 ⋕[T, d] L2 → L1 ⋕⋕[T, d] L2.
#L1 #T @(f2_ind … rfw … L1 T) -L1 -T
#n #IH #L1 * * /3 width=3 by lleqa_gref, lleqa_sort, lleq_fwd_length/
[ #i #Hn #L2 #d #H elim (lleq_fwd_lref … H) [ * || * ]
  /4 width=9 by lleqa_free, lleqa_lref, lleqa_skip, lleq_fwd_length, ldrop_fwd_rfw/
| #a #I #V #T #Hn #L2 #d #H elim (lleq_inv_bind … H) -H /3 width=1 by lleqa_bind/
| #I #V #T #Hn #L2 #d #H elim (lleq_inv_flat … H) -H /3 width=1 by lleqa_flat/
]
qed.

(* Advanced eliminators *****************************************************)

lemma lleq_ind_alt: ∀R:relation4 ynat term lenv lenv. (
                       ∀L1,L2,d,k. |L1| = |L2| → R d (⋆k) L1 L2
                    ) → (
                       ∀L1,L2,d,i. |L1| = |L2| → yinj i < d → R d (#i) L1 L2
                    ) → (
                       ∀I1,I2,L1,L2,K1,K2,V,d,i. d ≤ yinj i →
                       ⇩[i] L1 ≡ K1.ⓑ{I1}V → ⇩[i] L2 ≡ K2.ⓑ{I2}V →
                       K1 ⋕[V, yinj O] K2 → R (yinj O) V K1 K2 → R d (#i) L1 L2
                    ) → (
                       ∀L1,L2,d,i. |L1| = |L2| → |L1| ≤ i → |L2| ≤ i → R d (#i) L1 L2
                    ) → (
                       ∀L1,L2,d,p. |L1| = |L2| → R d (§p) L1 L2
                    ) → (
                       ∀a,I,L1,L2,V,T,d.
                       L1 ⋕[V, d]L2 → L1.ⓑ{I}V ⋕[T, ⫯d] L2.ⓑ{I}V →
                       R d V L1 L2 → R (⫯d) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) → R d (ⓑ{a,I}V.T) L1 L2
                    ) → (
                       ∀I,L1,L2,V,T,d.
                       L1 ⋕[V, d]L2 → L1 ⋕[T, d] L2 →
                       R d V L1 L2 → R d T L1 L2 → R d (ⓕ{I}V.T) L1 L2
                    ) →
                    ∀d,T,L1,L2. L1 ⋕[T, d] L2 → R d T L1 L2.
#R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #d #T #L1 #L2 #H elim (lleq_lleqa … H) -H
/3 width=9 by lleqa_inv_lleq/
qed-.
