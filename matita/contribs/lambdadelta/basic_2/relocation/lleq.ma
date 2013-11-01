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

include "basic_2/notation/relations/lazyeq_3.ma".
include "basic_2/relocation/ldrop.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

inductive lleq: term → relation lenv ≝
| lleq_sort: ∀L1,L2,k. |L1| = |L2| → lleq (⋆k) L1 L2
| lleq_lref: ∀I,L1,L2,K1,K2,V,i.
             ⇩[0, i] L1 ≡ K1.ⓑ{I}V → ⇩[0, i] L2 ≡ K2.ⓑ{I}V →
             lleq V K1 K2 → lleq (#i) L1 L2
| lleq_free: ∀L1,L2,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → lleq (#i) L1 L2
| lleq_gref: ∀L1,L2,p. |L1| = |L2| → lleq (§p) L1 L2
| lleq_bind: ∀a,I,L1,L2,V,T.
             lleq V L1 L2 → lleq T (L1.ⓑ{I}V) (L2.ⓑ{I}V) →
             lleq (ⓑ{a,I}V.T) L1 L2
| lleq_flat: ∀I,L1,L2,V,T.
             lleq V L1 L2 → lleq T L1 L2 → lleq (ⓕ{I}V.T) L1 L2
.

interpretation
   "lazy equivalence (local environment)"
   'LazyEq T L1 L2 = (lleq T L1 L2).

(* Basic_properties *********************************************************)

lemma lleq_sym: ∀T. symmetric … (lleq T).
#T #L1 #L2 #H elim H -T -L1 -L2
/2 width=7 by lleq_sort, lleq_lref, lleq_free, lleq_gref, lleq_bind, lleq_flat/
qed-.

lemma lleq_refl: ∀T. reflexive … (lleq T).
#T #L @(f2_ind … rfw … L T)
#n #IH #L * * /3 width=1 by lleq_sort, lleq_gref, lleq_bind, lleq_flat/
#i #H elim (lt_or_ge i (|L|)) /2 width=1 by lleq_free/
#HiL elim (ldrop_O1_lt … HiL) -HiL destruct /4 width=7 by lleq_lref, ldrop_fwd_rfw/
qed.

(* Basic inversion lemmas ***************************************************)

fact lleq_inv_lref_aux: ∀X,L1,L2. L1 ⋕[X] L2 → ∀i. X = #i →
                        (|L1| ≤ i ∧ |L2| ≤ i) ∨
                        ∃∃I,K1,K2,V. ⇩[0, i] L1 ≡ K1.ⓑ{I}V &
                                     ⇩[0, i] L2 ≡ K2.ⓑ{I}V &
                                     K1 ⋕[V] K2.
#X #L1 #L2 * -X -L1 -L2
[ #L1 #L2 #k #_ #j #H destruct
| #I #L1 #L2 #K1 #K2 #V #i #HLK1 #HLK2 #HK12 #j #H destruct /3 width=7 by ex3_4_intro, or_intror/
| #L1 #L2 #i #HL1 #HL2 #_ #j #H destruct /3 width=1 by or_introl, conj/
| #L1 #L2 #p #_ #j #H destruct
| #a #I #L1 #L2 #V #T #_ #_ #j #H destruct
| #I #L1 #L2 #V #T #_ #_ #j #H destruct
]
qed-.

lemma lleq_inv_lref: ∀L1,L2,i. L1 ⋕[#i] L2 →
                     (|L1| ≤ i ∧ |L2| ≤ i) ∨
                     ∃∃I,K1,K2,V. ⇩[0, i] L1 ≡ K1.ⓑ{I}V &
                                  ⇩[0, i] L2 ≡ K2.ⓑ{I}V &
                                  K1 ⋕[V] K2.
/2 width=3 by lleq_inv_lref_aux/ qed-.

fact lleq_inv_bind_aux: ∀X,L1,L2. L1 ⋕[X] L2 → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                        L1 ⋕[V] L2 ∧ L1.ⓑ{I}V ⋕[T] L2.ⓑ{I}V.
#X #L1 #L2 * -X -L1 -L2
[ #L1 #L2 #k #_ #b #J #W #U #H destruct
| #I #L1 #L2 #K1 #K2 #V #i #_ #_ #_ #b #J #W #U #H destruct
| #L1 #L2 #i #_ #_ #_ #b #J #W #U #H destruct
| #L1 #L2 #p #_ #b #J #W #U #H destruct
| #a #I #L1 #L2 #V #T #HV #HT #b #J #W #U #H destruct /2 width=1 by conj/
| #I #L1 #L2 #V #T #_ #_ #b #J #W #U #H destruct
]
qed-.

lemma lleq_inv_bind: ∀a,I,L1,L2,V,T. L1 ⋕[ ⓑ{a,I}V.T] L2 →
                     L1 ⋕[V] L2 ∧ L1.ⓑ{I}V ⋕[T] L2.ⓑ{I}V.
/2 width=4 by lleq_inv_bind_aux/ qed-.

fact lleq_inv_flat_aux: ∀X,L1,L2. L1 ⋕[X] L2 → ∀I,V,T. X = ⓕ{I}V.T →
                        L1 ⋕[V] L2 ∧ L1 ⋕[T] L2.
#X #L1 #L2 * -X -L1 -L2
[ #L1 #L2 #k #_ #J #W #U #H destruct
| #I #L1 #L2 #K1 #K2 #V #i #_ #_ #_ #J #W #U #H destruct
| #L1 #L2 #i #_ #_ #_ #J #W #U #H destruct
| #L1 #L2 #p #_ #J #W #U #H destruct
| #a #I #L1 #L2 #V #T #_ #_ #J #W #U #H destruct
| #I #L1 #L2 #V #T #HV #HT #J #W #U #H destruct /2 width=1 by conj/
]
qed-.

lemma lleq_inv_flat: ∀I,L1,L2,V,T. L1 ⋕[ ⓕ{I}V.T] L2 →
                     L1 ⋕[V] L2 ∧ L1 ⋕[T] L2.
/2 width=4 by lleq_inv_flat_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lleq_fwd_length: ∀L1,L2,T. L1 ⋕[T] L2 → |L1| = |L2|.
#L1 #L2 #T #H elim H -L1 -L2 -T //
#I #L1 #L2 #K1 #K2 #V #i #HLK1 #HLK2 #_ #IHK12
lapply (ldrop_fwd_length … HLK1) -HLK1
lapply (ldrop_fwd_length … HLK2) -HLK2
normalize //
qed-.

lemma lleq_fwd_ldrop_sn: ∀L1,L2,T. L1 ⋕[T] L2 → ∀K1,i. ⇩[0, i] L1 ≡ K1 →
                         ∃K2. ⇩[0, i] L2 ≡ K2.
#L1 #L2 #T #H #K1 #i #HLK1 lapply (lleq_fwd_length … H) -H
#HL12 lapply (ldrop_fwd_length_le2 … HLK1) -HLK1 /2 width=1 by ldrop_O1_le/ (**) (* full auto fails *)
qed-.
