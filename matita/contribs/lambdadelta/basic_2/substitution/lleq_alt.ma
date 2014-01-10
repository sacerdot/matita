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

inductive lleqa: relation4 ynat term lenv lenv ≝
| lleqa_sort: ∀L1,L2,d,k. |L1| = |L2| → lleqa d (⋆k) L1 L2
| lleqa_skip: ∀L1,L2,d,i. |L1| = |L2| → yinj i < d → lleqa d (#i) L1 L2
| lleqa_lref: ∀I1,I2,L1,L2,K1,K2,V,d,i. d ≤ yinj i →
              ⇩[0, i] L1 ≡ K1.ⓑ{I1}V → ⇩[0, i] L2 ≡ K2.ⓑ{I2}V →
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
                       ⇩[O, i] L1 ≡ K1.ⓑ{I1}V → ⇩[O, i] L2 ≡ K2.ⓑ{I2}V →
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

(* Advanced inversion lemmas ************************************************)

fact lleq_inv_S_aux: ∀L1,L2,T,d0. L1 ⋕[T, d0] L2 → ∀d. d0 = d + 1 →
                     ∀K1,K2,I,V. ⇩[0, d] L1 ≡ K1.ⓑ{I}V → ⇩[0, d] L2 ≡ K2.ⓑ{I}V →
                     K1 ⋕[V, 0] K2 → L1 ⋕[T, d] L2.
#L1 #L2 #T #d0 #H @(lleq_ind_alt … H) -L1 -L2 -T -d0
/2 width=1 by lleq_gref, lleq_free, lleq_sort/
[ #L1 #L2 #d0 #i #HL12 #Hid #d #H #K1 #K2 #I #V #HLK1 #HLK2 #HV destruct
  elim (yle_split_eq i d) /2 width=1 by lleq_skip, ylt_fwd_succ2/ -HL12 -Hid
  #H destruct /2 width=8 by lleq_lref/
| #I1 #I2 #L1 #L2 #K11 #K22 #V #d0 #i #Hd0i #HLK11 #HLK22 #HV #_ #d #H #K1 #K2 #J #W #_ #_ #_ destruct
  /3 width=8 by lleq_lref, yle_pred_sn/
| #a #I #L1 #L2 #V #T #d0 #_ #_ #IHV #IHT #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /4 width=7 by lleq_bind, ldrop_ldrop/
| #I #L1 #L2 #V #T #d0 #_ #_ #IHV #IHT #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /3 width=7 by lleq_flat/
]
qed-.

lemma lleq_inv_S: ∀T,L1,L2,d. L1 ⋕[T, d+1] L2 →
                  ∀K1,K2,I,V. ⇩[0, d] L1 ≡ K1.ⓑ{I}V → ⇩[0, d] L2 ≡ K2.ⓑ{I}V →
                  K1 ⋕[V, 0] K2 → L1 ⋕[T, d] L2.
/2 width=7 by lleq_inv_S_aux/ qed-.

lemma lleq_inv_bind_O: ∀a,I,L1,L2,V,T. L1 ⋕[ⓑ{a,I}V.T, 0] L2 →
                       L1 ⋕[V, 0] L2 ∧ L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V.
#a #I #L1 #L2 #V #T #H elim (lleq_inv_bind … H) -H
/3 width=7 by ldrop_pair, conj, lleq_inv_S/
qed-.

(* Advanced properties ******************************************************)

lemma lleq_ge: ∀L1,L2,T,d1. L1 ⋕[T, d1] L2 → ∀d2. d1 ≤ d2 → L1 ⋕[T, d2] L2.
#L1 #L2 #T #d1 #H @(lleq_ind_alt … H) -L1 -L2 -T -d1
/4 width=1 by lleq_sort, lleq_free, lleq_gref, lleq_bind, lleq_flat, yle_succ/
[ /3 width=3 by lleq_skip, ylt_yle_trans/
| #I1 #I2 #L1 #L2 #K1 #K2 #V #d1 #i #Hi #HLK1 #HLK2 #HV #IHV #d2 #Hd12 elim (ylt_split i d2)
  [ lapply (lleq_fwd_length … HV) #HK12 #Hid2
    lapply (ldrop_fwd_length … HLK1) lapply (ldrop_fwd_length … HLK2)
    normalize in ⊢ (%→%→?); -I1 -I2 -V -d1 /2 width=1 by lleq_skip/ 
  | /3 width=8 by lleq_lref, yle_trans/
  ]
]
qed-.

lemma lleq_bind_O: ∀a,I,L1,L2,V,T. L1 ⋕[V, 0] L2 → L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V →
                   L1 ⋕[ⓑ{a,I}V.T, 0] L2.
/3 width=3 by lleq_ge, lleq_bind/ qed.

lemma lleq_bind_repl_SO: ∀I,L1,L2,V,T. L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V →
                         ∀J,W. L1.ⓑ{J}W ⋕[T, 1] L2.ⓑ{J}W.
#I #L1 #L2 #V #T #HT #J #W lapply (lleq_ge … HT 1 ?) // -HT
#HT @(lleq_lsuby_repl … HT) /2 width=1 by lsuby_succ/ (**) (* full auto fails *)
qed-.

lemma lleq_bind_repl_O: ∀I,L1,L2,V,T. L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V →
                        ∀J,W. L1 ⋕[W, 0] L2 → L1.ⓑ{J}W ⋕[T, 0] L2.ⓑ{J}W.
/3 width=7 by lleq_bind_repl_SO, lleq_inv_S/ qed-.
