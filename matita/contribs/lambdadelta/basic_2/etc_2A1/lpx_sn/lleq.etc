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

include "basic_2/notation/relations/lazyeq_4.ma".
include "basic_2/substitution/llpx_sn.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

definition ceq: relation4 bind2 lenv term term ≝ λI,L,T1,T2. T1 = T2.

definition lleq: relation4 ynat term lenv lenv ≝ llpx_sn ceq.

interpretation
   "lazy equivalence (local environment)"
   'LazyEq T d L1 L2 = (lleq d T L1 L2).

definition lleq_transitive: predicate (relation4 bind2 lenv term term) ≝
           λR. ∀I,L2,T1,T2. R I L2 T1 T2 → ∀L1. L1 ≡[T1, 0] L2 → R I L1 T1 T2.

(* Basic inversion lemmas ***************************************************)

lemma lleq_ind: ∀R:relation4 ynat term lenv lenv. (
                   ∀L1,L2,d,k. |L1| = |L2| → R d (⋆k) L1 L2
                ) → (
                   ∀L1,L2,d,i. |L1| = |L2| → yinj i < d → R d (#i) L1 L2
                ) → (
                   ∀I,L1,L2,K1,K2,V,d,i. d ≤ yinj i →
                   ⇩[i] L1 ≡ K1.ⓑ{I}V → ⇩[i] L2 ≡ K2.ⓑ{I}V →
                   K1 ≡[V, yinj O] K2 → R (yinj O) V K1 K2 → R d (#i) L1 L2
                ) → (
                   ∀L1,L2,d,i. |L1| = |L2| → |L1| ≤ i → |L2| ≤ i → R d (#i) L1 L2
                ) → (
                   ∀L1,L2,d,p. |L1| = |L2| → R d (§p) L1 L2
                ) → (
                   ∀a,I,L1,L2,V,T,d.
                   L1 ≡[V, d]L2 → L1.ⓑ{I}V ≡[T, ⫯d] L2.ⓑ{I}V →
                   R d V L1 L2 → R (⫯d) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) → R d (ⓑ{a,I}V.T) L1 L2
                ) → (
                   ∀I,L1,L2,V,T,d.
                   L1 ≡[V, d]L2 → L1 ≡[T, d] L2 →
                   R d V L1 L2 → R d T L1 L2 → R d (ⓕ{I}V.T) L1 L2
                ) →
                ∀d,T,L1,L2. L1 ≡[T, d] L2 → R d T L1 L2.
#R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #d #T #L1 #L2 #H elim H -L1 -L2 -T -d /2 width=8 by/
qed-.

lemma lleq_inv_bind: ∀a,I,L1,L2,V,T,d. L1 ≡[ⓑ{a,I}V.T, d] L2 →
                     L1 ≡[V, d] L2 ∧ L1.ⓑ{I}V ≡[T, ⫯d] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_inv_bind/ qed-.

lemma lleq_inv_flat: ∀I,L1,L2,V,T,d. L1 ≡[ⓕ{I}V.T, d] L2 →
                     L1 ≡[V, d] L2 ∧ L1 ≡[T, d] L2.
/2 width=2 by llpx_sn_inv_flat/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lleq_fwd_length: ∀L1,L2,T,d. L1 ≡[T, d] L2 → |L1| = |L2|.
/2 width=4 by llpx_sn_fwd_length/ qed-.

lemma lleq_fwd_lref: ∀L1,L2,d,i. L1 ≡[#i, d] L2 →
                     ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                      | yinj i < d
                      | ∃∃I,K1,K2,V. ⇩[i] L1 ≡ K1.ⓑ{I}V &
                                     ⇩[i] L2 ≡ K2.ⓑ{I}V &
                                      K1 ≡[V, yinj 0] K2 & d ≤ yinj i.
#L1 #L2 #d #i #H elim (llpx_sn_fwd_lref … H) /2 width=1/
* /3 width=7 by or3_intro2, ex4_4_intro/
qed-.

lemma lleq_fwd_ldrop_sn: ∀L1,L2,T,d. L1 ≡[d, T] L2 → ∀K1,i. ⇩[i] L1 ≡ K1 →
                         ∃K2. ⇩[i] L2 ≡ K2.
/2 width=7 by llpx_sn_fwd_ldrop_sn/ qed-.

lemma lleq_fwd_ldrop_dx: ∀L1,L2,T,d. L1 ≡[d, T] L2 → ∀K2,i. ⇩[i] L2 ≡ K2 →
                         ∃K1. ⇩[i] L1 ≡ K1.
/2 width=7 by llpx_sn_fwd_ldrop_dx/ qed-.

lemma lleq_fwd_bind_sn: ∀a,I,L1,L2,V,T,d.
                        L1 ≡[ⓑ{a,I}V.T, d] L2 → L1 ≡[V, d] L2.
/2 width=4 by llpx_sn_fwd_bind_sn/ qed-.

lemma lleq_fwd_bind_dx: ∀a,I,L1,L2,V,T,d.
                        L1 ≡[ⓑ{a,I}V.T, d] L2 → L1.ⓑ{I}V ≡[T, ⫯d] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_fwd_bind_dx/ qed-.

lemma lleq_fwd_flat_sn: ∀I,L1,L2,V,T,d.
                        L1 ≡[ⓕ{I}V.T, d] L2 → L1 ≡[V, d] L2.
/2 width=3 by llpx_sn_fwd_flat_sn/ qed-.

lemma lleq_fwd_flat_dx: ∀I,L1,L2,V,T,d.
                        L1 ≡[ⓕ{I}V.T, d] L2 → L1 ≡[T, d] L2.
/2 width=3 by llpx_sn_fwd_flat_dx/ qed-.

(* Basic properties *********************************************************)

lemma lleq_sort: ∀L1,L2,d,k. |L1| = |L2| → L1 ≡[⋆k, d] L2.
/2 width=1 by llpx_sn_sort/ qed.

lemma lleq_skip: ∀L1,L2,d,i. yinj i < d → |L1| = |L2| → L1 ≡[#i, d] L2.
/2 width=1 by llpx_sn_skip/ qed.

lemma lleq_lref: ∀I,L1,L2,K1,K2,V,d,i. d ≤ yinj i →
                 ⇩[i] L1 ≡ K1.ⓑ{I}V → ⇩[i] L2 ≡ K2.ⓑ{I}V →
                 K1 ≡[V, 0] K2 → L1 ≡[#i, d] L2.
/2 width=9 by llpx_sn_lref/ qed.

lemma lleq_free: ∀L1,L2,d,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → L1 ≡[#i, d] L2.
/2 width=1 by llpx_sn_free/ qed.

lemma lleq_gref: ∀L1,L2,d,p. |L1| = |L2| → L1 ≡[§p, d] L2.
/2 width=1 by llpx_sn_gref/ qed.

lemma lleq_bind: ∀a,I,L1,L2,V,T,d.
                 L1 ≡[V, d] L2 → L1.ⓑ{I}V ≡[T, ⫯d] L2.ⓑ{I}V →
                 L1 ≡[ⓑ{a,I}V.T, d] L2.
/2 width=1 by llpx_sn_bind/ qed.

lemma lleq_flat: ∀I,L1,L2,V,T,d.
                 L1 ≡[V, d] L2 → L1 ≡[T, d] L2 → L1 ≡[ⓕ{I}V.T, d] L2.
/2 width=1 by llpx_sn_flat/ qed.

lemma lleq_refl: ∀d,T. reflexive … (lleq d T).
/2 width=1 by llpx_sn_refl/ qed.

lemma lleq_Y: ∀L1,L2,T. |L1| = |L2| → L1 ≡[T, ∞] L2.
/2 width=1 by llpx_sn_Y/ qed.

lemma lleq_sym: ∀d,T. symmetric … (lleq d T).
#d #T #L1 #L2 #H @(lleq_ind … H) -d -T -L1 -L2
/2 width=7 by lleq_sort, lleq_skip, lleq_lref, lleq_free, lleq_gref, lleq_bind, lleq_flat/
qed-.

lemma lleq_ge_up: ∀L1,L2,U,dt. L1 ≡[U, dt] L2 →
                  ∀T,d,e. ⇧[d, e] T ≡ U →
                  dt ≤ d + e → L1 ≡[U, d] L2.
/2 width=6 by llpx_sn_ge_up/ qed-.

lemma lleq_ge: ∀L1,L2,T,d1. L1 ≡[T, d1] L2 → ∀d2. d1 ≤ d2 → L1 ≡[T, d2] L2.
/2 width=3 by llpx_sn_ge/ qed-.

lemma lleq_bind_O: ∀a,I,L1,L2,V,T. L1 ≡[V, 0] L2 → L1.ⓑ{I}V ≡[T, 0] L2.ⓑ{I}V →
                   L1 ≡[ⓑ{a,I}V.T, 0] L2.
/2 width=1 by llpx_sn_bind_O/ qed-.

(* Advancded properties on lazy pointwise exyensions ************************)

lemma llpx_sn_lrefl: ∀R. (∀I,L. reflexive … (R I L)) →
                     ∀L1,L2,T,d. L1 ≡[T, d] L2 → llpx_sn R d T L1 L2.
/2 width=3 by llpx_sn_co/ qed-.
