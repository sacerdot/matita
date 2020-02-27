(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/relocation/rtmap_eq.ma".

(* RELOCATION N-STREAM ******************************************************)

(* Specific properties ******************************************************)

fact eq_inv_seq_aux: ∀f1,f2,n1,n2. n1⨮f1 ≡ n2⨮f2 → n1 = n2 ∧ f1 ≡ f2.
#f1 #f2 #n1 #n2 @(nat_elim2 … n1 n2) -n1 -n2
[ #n2 #H elim (eq_inv_px … H) -H [2,3: // ]
  #g1 #H1 #H elim (push_inv_seq_dx … H) -H /2 width=1 by conj/
| #n1 #H elim (eq_inv_np … H) -H //
| #n1 #n2 #IH #H lapply (eq_inv_nn … H ????) -H [1,2,3,4: // ]
  #H elim (IH H) -IH -H /2 width=1 by conj/
]
qed-.

lemma eq_inv_seq: ∀g1,g2. g1 ≡ g2 → ∀f1,f2,n1,n2. n1⨮f1 = g1 → n2⨮f2 = g2 →
                  n1 = n2 ∧ f1 ≡ f2.
/2 width=1 by eq_inv_seq_aux/ qed-.

corec lemma nstream_eq: ∀f1,f2. f1 ≡ f2 → f1 ≗ f2.
* #n1 #f1 * #n2 #f2 #Hf cases (eq_inv_gen … Hf) -Hf *
#g1 #g2 #Hg #H1 #H2
[ cases (push_inv_seq_dx … H1) -H1 * -n1 #H1
  cases (push_inv_seq_dx … H2) -H2 * -n2 #H2
  @eq_seq /2 width=1 by/
| cases (next_inv_seq_dx … H1) -H1 #m1 #H1 * -n1
  cases (next_inv_seq_dx … H2) -H2 #m2 #H2 * -n2
  cases (eq_inv_seq … Hg … H1 H2) -g1 -g2 #Hm #Hf
  @eq_seq /2 width=1 by/
]
qed-.

corec lemma nstream_inv_eq: ∀f1,f2. f1 ≗ f2 → f1 ≡ f2.
* #n1 #f1 * #n2 #f2 #H cases (eq_stream_inv_seq ??? H) -H [2,3,4,5,6,7: // ]
#Hf * -n2 cases n1 -n1 /3 width=5 by eq_push/
#n @eq_next /3 width=5 by eq_seq/
qed.

lemma eq_seq_id: ∀f1,f2. f1 ≡ f2 → ∀n. n⨮f1 ≡ n⨮f2.
/4 width=1 by nstream_inv_eq, nstream_eq, eq_seq/ qed.
