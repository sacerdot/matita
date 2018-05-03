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

include "ground_2/notation/functions/upspoon_1.ma".
include "ground_2/lib/streams_tls.ma".

(* RELOCATION N-STREAM ******************************************************)

definition rtmap: Type[0] ≝ stream nat.

definition push: rtmap → rtmap ≝ λf. 0⨮f.

interpretation "push (nstream)" 'UpSpoon f = (push f).

definition next: rtmap → rtmap.
* #n #f @(↑n⨮f)
defined.

interpretation "next (nstream)" 'UpArrow f = (next f).

(* Basic properties *********************************************************)

lemma push_rew: ∀f. 0⨮f = ⫯f.
// qed.

lemma next_rew: ∀f,n. (↑n)⨮f = ↑(n⨮f).
// qed.

(* Basic inversion lemmas ***************************************************)

lemma injective_push: injective ? ? push.
#f1 #f2 normalize #H destruct //
qed-.

lemma discr_push_next: ∀f1,f2. ⫯f1 = ↑f2 → ⊥.
#f1 * #n2 #f2 normalize #H destruct
qed-.

lemma discr_next_push: ∀f1,f2. ↑f1 = ⫯f2 → ⊥.
* #n1 #f1 #f2 normalize #H destruct
qed-.

lemma injective_next: injective ? ? next.
* #n1 #f1 * #n2 #f2 normalize #H destruct //
qed-.

lemma push_inv_seq_sn: ∀f,g,n. n⨮g = ⫯f → 0 = n ∧ g = f.
#f #g #n <push_rew #H destruct /2 width=1 by conj/
qed-.

lemma push_inv_seq_dx: ∀f,g,n. ⫯f = n⨮g → 0 = n ∧ g = f.
#f #g #n <push_rew #H destruct /2 width=1 by conj/
qed-.

lemma next_inv_seq_sn: ∀f,g,n. n⨮g = ↑f → ∃∃m. m⨮g = f & ↑m = n.
* #m #f #g #n <next_rew #H destruct /2 width=3 by ex2_intro/
qed-.

lemma next_inv_seq_dx: ∀f,g,n. ↑f = n⨮g → ∃∃m. m⨮g = f & ↑m = n.
* #m #f #g #n <next_rew #H destruct /2 width=3 by ex2_intro/
qed-.

lemma case_prop: ∀R:predicate rtmap.
                 (∀f. R (⫯f)) → (∀f. R (↑f)) → ∀f. R f.
#R #H1 #H2 * * //
qed-.

lemma case_type0: ∀R:rtmap→Type[0].
                  (∀f. R (⫯f)) → (∀f. R (↑f)) → ∀f. R f.
#R #H1 #H2 * * //
qed-.

lemma iota_push: ∀R,a,b,f. a f = case_type0 R a b (⫯f).
// qed.

lemma iota_next: ∀R,a,b,f. b f = case_type0 R a b (↑f).
#R #a #b * //
qed.

(* Specific properties ******************************************************)

lemma tl_push: ∀f. f = ⫰⫯f.
// qed.

lemma tl_next: ∀f. ⫰f = ⫰↑f.
* // qed.
