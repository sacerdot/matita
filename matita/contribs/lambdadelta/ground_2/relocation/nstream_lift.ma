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

include "ground_2/notation/functions/lift_1.ma".
include "ground_2/relocation/nstream.ma".

(* RELOCATION N-STREAM ******************************************************)

definition push: rtmap → rtmap ≝ λf. 0@f.

interpretation "push (nstream)" 'Lift f = (push f).

definition next: rtmap → rtmap.
* #n #f @(⫯n@f)
qed.

interpretation "next (nstream)" 'Successor f = (next f).

(* Basic properties *********************************************************)

lemma push_rew: ∀f. ↑f = 0@f.
// qed.

lemma next_rew: ∀f,n. ⫯(n@f) = (⫯n)@f.
// qed.

lemma next_rew_sn: ∀f,n1,n2. n1 = ⫯n2 → n1@f = ⫯(n2@f).
// qed.

(* Basic inversion lemmas ***************************************************)

lemma injective_push: injective ? ? push.
#f1 #f2 normalize #H destruct //
qed-.

lemma discr_push_next: ∀f1,f2. ↑f1 = ⫯f2 → ⊥.
#f1 * #n2 #f2 normalize #H destruct
qed-.

lemma discr_next_push: ∀f1,f2. ⫯f1 = ↑f2 → ⊥.
* #n1 #f1 #f2 normalize #H destruct
qed-.

lemma injective_next: injective ? ? next.
* #n1 #f1 * #n2 #f2 normalize #H destruct //
qed-.

lemma push_inv_seq_sn: ∀f,g,n. n@g = ↑f → n = 0 ∧ g = f.
#f #g #n >push_rew #H destruct /2 width=1 by conj/
qed-.

lemma push_inv_seq_dx: ∀f,g,n. ↑f = n@g → n = 0 ∧ g = f.
#f #g #n >push_rew #H destruct /2 width=1 by conj/
qed-.

lemma next_inv_seq_sn: ∀f,g,n. n@g = ⫯f → ∃∃m. n = ⫯m & f = m@g.
* #m #f #g #n >next_rew #H destruct /2 width=3 by ex2_intro/
qed-.

lemma next_inv_seq_dx: ∀f,g,n. ⫯f = n@g → ∃∃m. n = ⫯m & f = m@g.
* #m #f #g #n >next_rew #H destruct /2 width=3 by ex2_intro/
qed-.
