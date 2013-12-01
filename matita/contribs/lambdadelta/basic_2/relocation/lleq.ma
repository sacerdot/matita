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
include "basic_2/relocation/ldrop.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

inductive lleq: nat → term → relation lenv ≝
| lleq_sort: ∀L1,L2,d,k. |L1| = |L2| → lleq d (⋆k) L1 L2
| lleq_skip: ∀I1,I2,L1,L2,K1,K2,V1,V2,d,i. i < d →
             ⇩[0, i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[0, i] L2 ≡ K2.ⓑ{I2}V2 →
             lleq (d-i-1) V1 K1 K2 → lleq (d-i-1) V2 K1 K2 → lleq d (#i) L1 L2
| lleq_lref: ∀I,L1,L2,K1,K2,V,d,i. d ≤ i →
             ⇩[0, i] L1 ≡ K1.ⓑ{I}V → ⇩[0, i] L2 ≡ K2.ⓑ{I}V →
             lleq 0 V K1 K2 → lleq d (#i) L1 L2
| lleq_free: ∀L1,L2,d,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → lleq d (#i) L1 L2
| lleq_gref: ∀L1,L2,d,p. |L1| = |L2| → lleq d (§p) L1 L2
| lleq_bind: ∀a,I,L1,L2,V,T,d.
             lleq d V L1 L2 → lleq (d+1) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) →
             lleq d (ⓑ{a,I}V.T) L1 L2
| lleq_flat: ∀I,L1,L2,V,T,d.
             lleq d V L1 L2 → lleq d T L1 L2 → lleq d (ⓕ{I}V.T) L1 L2
.

interpretation
   "lazy equivalence (local environment)"
   'LazyEq d T L1 L2 = (lleq d T L1 L2).

(* Basic_properties *********************************************************)

lemma lleq_sym: ∀d,T. symmetric … (lleq d T).
#d #T #L1 #L2 #H elim H -d -T -L1 -L2
/2 width=10 by lleq_sort, lleq_skip, lleq_lref, lleq_free, lleq_gref, lleq_bind, lleq_flat/
qed-.

(* Note this is: "∀d,T. reflexive … (lleq d T)" *)
axiom lleq_refl: ∀T,L,d. L ⋕[d, T] L.
(*
#T #L @(f2_ind … rfw … L T) -L -T
#n #IH #L * * /3 width=1 by lleq_sort, lleq_gref, lleq_bind, lleq_flat/
#i #H elim (lt_or_ge i (|L|)) /2 width=1 by lleq_free/
#HiL #d elim (lt_or_ge i d) /2 width=1 by lleq_skip/
elim (ldrop_O1_lt … HiL) -HiL destruct /4 width=7 by lleq_lref, ldrop_fwd_rfw/
qed.
*)

lemma lleq_ge: ∀L1,L2,T,d1. L1 ⋕[d1, T] L2 → ∀d2. d1 ≤ d2 → L1 ⋕[d2, T] L2.
#L1 #L2 #T #d1 #H elim H -L1 -L2 -T -d1
/4 width=1 by lleq_sort, lleq_free, lleq_gref, lleq_bind, lleq_flat, le_S_S/
[ /5 width=10 by lleq_skip, lt_to_le_to_lt, monotonic_le_minus_l, monotonic_pred/ (**) (* a bit slow *)
| #I #L1 #L2 #K1 #K2 #V #d1 #i #Hi #HLK1 #HLK2 #HV #IHV #d2 #Hd12 elim (lt_or_ge i d2)
  [ -d1 /3 width=10 by lleq_skip/
  | /3 width=7 by lleq_lref, transitive_le/
  ]
]
qed-.

(* Basic inversion lemmas ***************************************************)

fact lleq_inv_lref_aux: ∀d,X,L1,L2. L1 ⋕[d, X] L2 → ∀i. X = #i →
                        ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                         | ∃∃I1,I2,K1,K2,V1,V2. ⇩[0, i] L1 ≡ K1.ⓑ{I1}V1 &
                                                ⇩[0, i] L2 ≡ K2.ⓑ{I2}V2 &
                                                K1 ⋕[d-i-1, V1] K2 &
                                                K1 ⋕[d-i-1, V2] K2 &
                                                i < d
                         | ∃∃I,K1,K2,V. ⇩[0, i] L1 ≡ K1.ⓑ{I}V &
                                        ⇩[0, i] L2 ≡ K2.ⓑ{I}V &
                                        K1 ⋕[0, V] K2 & d ≤ i.
#d #X #L1 #L2 * -d -X -L1 -L2
[ #L1 #L2 #d #k #_ #j #H destruct
| #I1 #I2 #L1 #L2 #K1 #K2 #V1 #V2 #d #i #Hid #HLK1 #HLK2 #HV1 #HV2 #j #H destruct /3 width=10 by or3_intro1, ex5_6_intro/
| #I #L1 #L2 #K1 #K2 #V #d #i #Hdi #HLK1 #HLK2 #HK12 #j #H destruct /3 width=7 by or3_intro2, ex4_4_intro/
| #L1 #L2 #d #i #HL1 #HL2 #_ #j #H destruct /3 width=1 by or3_intro0, conj/
| #L1 #L2 #d #p #_ #j #H destruct
| #a #I #L1 #L2 #V #T #d #_ #_ #j #H destruct
| #I #L1 #L2 #V #T #d #_ #_ #j #H destruct
]
qed-.

lemma lleq_inv_lref: ∀L1,L2,d,i. L1 ⋕[d, #i] L2 →
                     ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                      | ∃∃I1,I2,K1,K2,V1,V2. ⇩[0, i] L1 ≡ K1.ⓑ{I1}V1 &
                                             ⇩[0, i] L2 ≡ K2.ⓑ{I2}V2 &
                                             K1 ⋕[d-i-1, V1] K2 &
                                             K1 ⋕[d-i-1, V2] K2 &
                                             i < d
                      | ∃∃I,K1,K2,V. ⇩[0, i] L1 ≡ K1.ⓑ{I}V &
                                     ⇩[0, i] L2 ≡ K2.ⓑ{I}V &
                                     K1 ⋕[0, V] K2 & d ≤ i.
/2 width=3 by lleq_inv_lref_aux/ qed-.

fact lleq_inv_bind_aux: ∀d,X,L1,L2. L1 ⋕[d,X] L2 → ∀a,I,V,T. X = ⓑ{a,I}V.T →
                        L1 ⋕[d, V] L2 ∧ L1.ⓑ{I}V ⋕[d+1, T] L2.ⓑ{I}V.
#d #X #L1 #L2 * -d -X -L1 -L2
[ #L1 #L2 #d #k #_ #b #J #W #U #H destruct
| #I1 #I2 #L1 #L2 #K1 #K2 #V1 #V2 #d #i #_ #_ #_ #_ #_ #b #J #W #U #H destruct
| #I #L1 #L2 #K1 #K2 #V #d #i #_ #_ #_ #_ #b #J #W #U #H destruct
| #L1 #L2 #d #i #_ #_ #_ #b #J #W #U #H destruct
| #L1 #L2 #d #p #_ #b #J #W #U #H destruct
| #a #I #L1 #L2 #V #T #d #HV #HT #b #J #W #U #H destruct /2 width=1 by conj/
| #I #L1 #L2 #V #T #d #_ #_ #b #J #W #U #H destruct
]
qed-.

lemma lleq_inv_bind: ∀a,I,L1,L2,V,T,d. L1 ⋕[d, ⓑ{a,I}V.T] L2 →
                     L1 ⋕[d, V] L2 ∧ L1.ⓑ{I}V ⋕[d+1, T] L2.ⓑ{I}V.
/2 width=4 by lleq_inv_bind_aux/ qed-.

fact lleq_inv_flat_aux: ∀d,X,L1,L2. L1 ⋕[d, X] L2 → ∀I,V,T. X = ⓕ{I}V.T →
                        L1 ⋕[d, V] L2 ∧ L1 ⋕[d, T] L2.
#d #X #L1 #L2 * -d -X -L1 -L2
[ #L1 #L2 #d #k #_ #J #W #U #H destruct
| #I1 #I2 #L1 #L2 #K1 #K2 #V1 #V2 #d #i #_ #_ #_ #_ #_ #J #W #U #H destruct
| #I #L1 #L2 #K1 #K2 #V #d #i #_ #_ #_ #_ #J #W #U #H destruct
| #L1 #L2 #d #i #_ #_ #_ #J #W #U #H destruct
| #L1 #L2 #d #p #_ #J #W #U #H destruct
| #a #I #L1 #L2 #V #T #d #_ #_ #J #W #U #H destruct
| #I #L1 #L2 #V #T #d #HV #HT #J #W #U #H destruct /2 width=1 by conj/
]
qed-.

lemma lleq_inv_flat: ∀I,L1,L2,V,T,d. L1 ⋕[d, ⓕ{I}V.T] L2 →
                     L1 ⋕[d, V] L2 ∧ L1 ⋕[d, T] L2.
/2 width=4 by lleq_inv_flat_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lleq_fwd_length: ∀L1,L2,T,d. L1 ⋕[d, T] L2 → |L1| = |L2|.
#L1 #L2 #T #d #H elim H -L1 -L2 -T -d //
[ #I1 #I2 #L1 #L2 #K1 #K2 #V1 #V2 #d #i #_ #HLK1 #HLK2 #_ #_ #HK12 #_
| #I #L1 #L2 #K1 #K2 #V #d #i #_ #HLK1 #HLK2 #_ #IHK12
]
lapply (ldrop_fwd_length … HLK1) -HLK1
lapply (ldrop_fwd_length … HLK2) -HLK2
normalize //
qed-.

lemma lleq_fwd_ldrop_sn: ∀L1,L2,T,d. L1 ⋕[d, T] L2 → ∀K1,i. ⇩[0, i] L1 ≡ K1 →
                         ∃K2. ⇩[0, i] L2 ≡ K2.
#L1 #L2 #T #d #H #K1 #i #HLK1 lapply (lleq_fwd_length … H) -H
#HL12 lapply (ldrop_fwd_length_le2 … HLK1) -HLK1 /2 width=1 by ldrop_O1_le/
qed-.

lemma lleq_fwd_ldrop_dx: ∀L1,L2,T,d. L1 ⋕[d, T] L2 → ∀K2,i. ⇩[0, i] L2 ≡ K2 →
                         ∃K1. ⇩[0, i] L1 ≡ K1.
/3 width=6 by lleq_fwd_ldrop_sn, lleq_sym/ qed-.
