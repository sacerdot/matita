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

include "ground_2/xoa/ex_4_4.ma".
include "basic_2A/notation/relations/lazyeq_4.ma".
include "basic_2A/multiple/llpx_sn.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

definition ceq: relation3 lenv term term ≝ λL,T1,T2. T1 = T2.

definition lleq: relation4 ynat term lenv lenv ≝ llpx_sn ceq.

interpretation
   "lazy equivalence (local environment)"
   'LazyEq T l L1 L2 = (lleq l T L1 L2).

definition lleq_transitive: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[T1, 0] L2 → R L1 T1 T2.

(* Basic inversion lemmas ***************************************************)

lemma lleq_ind: ∀R:relation4 ynat term lenv lenv. (
                   ∀L1,L2,l,k. |L1| = |L2| → R l (⋆k) L1 L2
                ) → (
                   ∀L1,L2,l,i. |L1| = |L2| → yinj i < l → R l (#i) L1 L2
                ) → (
                   ∀I,L1,L2,K1,K2,V,l,i. l ≤ yinj i →
                   ⬇[i] L1 ≡ K1.ⓑ{I}V → ⬇[i] L2 ≡ K2.ⓑ{I}V →
                   K1 ≡[V, yinj O] K2 → R (yinj O) V K1 K2 → R l (#i) L1 L2
                ) → (
                   ∀L1,L2,l,i. |L1| = |L2| → |L1| ≤ i → |L2| ≤ i → R l (#i) L1 L2
                ) → (
                   ∀L1,L2,l,p. |L1| = |L2| → R l (§p) L1 L2
                ) → (
                   ∀a,I,L1,L2,V,T,l.
                   L1 ≡[V, l]L2 → L1.ⓑ{I}V ≡[T, ↑l] L2.ⓑ{I}V →
                   R l V L1 L2 → R (↑l) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) → R l (ⓑ{a,I}V.T) L1 L2
                ) → (
                   ∀I,L1,L2,V,T,l.
                   L1 ≡[V, l]L2 → L1 ≡[T, l] L2 →
                   R l V L1 L2 → R l T L1 L2 → R l (ⓕ{I}V.T) L1 L2
                ) →
                ∀l,T,L1,L2. L1 ≡[T, l] L2 → R l T L1 L2.
#R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #l #T #L1 #L2 #H elim H -L1 -L2 -T -l /2 width=8 by/
qed-.

lemma lleq_inv_bind: ∀a,I,L1,L2,V,T,l. L1 ≡[ⓑ{a,I}V.T, l] L2 →
                     L1 ≡[V, l] L2 ∧ L1.ⓑ{I}V ≡[T, ↑l] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_inv_bind/ qed-.

lemma lleq_inv_flat: ∀I,L1,L2,V,T,l. L1 ≡[ⓕ{I}V.T, l] L2 →
                     L1 ≡[V, l] L2 ∧ L1 ≡[T, l] L2.
/2 width=2 by llpx_sn_inv_flat/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lleq_fwd_length: ∀L1,L2,T,l. L1 ≡[T, l] L2 → |L1| = |L2|.
/2 width=4 by llpx_sn_fwd_length/ qed-.

lemma lleq_fwd_lref: ∀L1,L2,l,i. L1 ≡[#i, l] L2 →
                     ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                      | yinj i < l
                      | ∃∃I,K1,K2,V. ⬇[i] L1 ≡ K1.ⓑ{I}V &
                                     ⬇[i] L2 ≡ K2.ⓑ{I}V &
                                      K1 ≡[V, yinj 0] K2 & l ≤ yinj i.
#L1 #L2 #l #i #H elim (llpx_sn_fwd_lref … H) /2 width=1 by or3_intro0, or3_intro1/
* /3 width=7 by or3_intro2, ex4_4_intro/
qed-.

lemma lleq_fwd_drop_sn: ∀L1,L2,T,l. L1 ≡[l, T] L2 → ∀K1,i. ⬇[i] L1 ≡ K1 →
                         ∃K2. ⬇[i] L2 ≡ K2.
/2 width=7 by llpx_sn_fwd_drop_sn/ qed-.

lemma lleq_fwd_drop_dx: ∀L1,L2,T,l. L1 ≡[l, T] L2 → ∀K2,i. ⬇[i] L2 ≡ K2 →
                         ∃K1. ⬇[i] L1 ≡ K1.
/2 width=7 by llpx_sn_fwd_drop_dx/ qed-.

lemma lleq_fwd_bind_sn: ∀a,I,L1,L2,V,T,l.
                        L1 ≡[ⓑ{a,I}V.T, l] L2 → L1 ≡[V, l] L2.
/2 width=4 by llpx_sn_fwd_bind_sn/ qed-.

lemma lleq_fwd_bind_dx: ∀a,I,L1,L2,V,T,l.
                        L1 ≡[ⓑ{a,I}V.T, l] L2 → L1.ⓑ{I}V ≡[T, ↑l] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_fwd_bind_dx/ qed-.

lemma lleq_fwd_flat_sn: ∀I,L1,L2,V,T,l.
                        L1 ≡[ⓕ{I}V.T, l] L2 → L1 ≡[V, l] L2.
/2 width=3 by llpx_sn_fwd_flat_sn/ qed-.

lemma lleq_fwd_flat_dx: ∀I,L1,L2,V,T,l.
                        L1 ≡[ⓕ{I}V.T, l] L2 → L1 ≡[T, l] L2.
/2 width=3 by llpx_sn_fwd_flat_dx/ qed-.

(* Basic properties *********************************************************)

lemma lleq_sort: ∀L1,L2,l,k. |L1| = |L2| → L1 ≡[⋆k, l] L2.
/2 width=1 by llpx_sn_sort/ qed.

lemma lleq_skip: ∀L1,L2,l,i. yinj i < l → |L1| = |L2| → L1 ≡[#i, l] L2.
/2 width=1 by llpx_sn_skip/ qed.

lemma lleq_lref: ∀I,L1,L2,K1,K2,V,l,i. l ≤ yinj i →
                 ⬇[i] L1 ≡ K1.ⓑ{I}V → ⬇[i] L2 ≡ K2.ⓑ{I}V →
                 K1 ≡[V, 0] K2 → L1 ≡[#i, l] L2.
/2 width=9 by llpx_sn_lref/ qed.

lemma lleq_free: ∀L1,L2,l,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → L1 ≡[#i, l] L2.
/2 width=1 by llpx_sn_free/ qed.

lemma lleq_gref: ∀L1,L2,l,p. |L1| = |L2| → L1 ≡[§p, l] L2.
/2 width=1 by llpx_sn_gref/ qed.

lemma lleq_bind: ∀a,I,L1,L2,V,T,l.
                 L1 ≡[V, l] L2 → L1.ⓑ{I}V ≡[T, ↑l] L2.ⓑ{I}V →
                 L1 ≡[ⓑ{a,I}V.T, l] L2.
/2 width=1 by llpx_sn_bind/ qed.

lemma lleq_flat: ∀I,L1,L2,V,T,l.
                 L1 ≡[V, l] L2 → L1 ≡[T, l] L2 → L1 ≡[ⓕ{I}V.T, l] L2.
/2 width=1 by llpx_sn_flat/ qed.

lemma lleq_refl: ∀l,T. reflexive … (lleq l T).
/2 width=1 by llpx_sn_refl/ qed.

lemma lleq_Y: ∀L1,L2,T. |L1| = |L2| → L1 ≡[T, ∞] L2.
/2 width=1 by llpx_sn_Y/ qed.

lemma lleq_sym: ∀l,T. symmetric … (lleq l T).
#l #T #L1 #L2 #H @(lleq_ind … H) -l -T -L1 -L2
/2 width=7 by lleq_sort, lleq_skip, lleq_lref, lleq_free, lleq_gref, lleq_bind, lleq_flat/
qed-.

lemma lleq_ge_up: ∀L1,L2,U,lt. L1 ≡[U, lt] L2 →
                  ∀T,l,m. ⬆[l, m] T ≡ U →
                  lt ≤ l + m → L1 ≡[U, l] L2.
/2 width=6 by llpx_sn_ge_up/ qed-.

lemma lleq_ge: ∀L1,L2,T,l1. L1 ≡[T, l1] L2 → ∀l2. l1 ≤ l2 → L1 ≡[T, l2] L2.
/2 width=3 by llpx_sn_ge/ qed-.

lemma lleq_bind_O: ∀a,I,L1,L2,V,T. L1 ≡[V, 0] L2 → L1.ⓑ{I}V ≡[T, 0] L2.ⓑ{I}V →
                   L1 ≡[ⓑ{a,I}V.T, 0] L2.
/2 width=1 by llpx_sn_bind_O/ qed-.

(* Advanceded properties on lazy pointwise extensions ************************)

lemma llpx_sn_lrefl: ∀R. (∀L. reflexive … (R L)) →
                     ∀L1,L2,T,l. L1 ≡[T, l] L2 → llpx_sn R l T L1 L2.
/2 width=3 by llpx_sn_co/ qed-.
