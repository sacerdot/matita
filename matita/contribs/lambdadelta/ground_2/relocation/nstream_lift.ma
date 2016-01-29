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
include "ground_2/relocation/nstream_at.ma".

(* RELOCATION N-STREAM ******************************************************)

definition push: nstream → nstream ≝ λt. 0@t.

interpretation "push (nstream)" 'Lift t = (push t).

definition next: nstream → nstream.
* #a #t @(⫯a@t)
qed.

interpretation "next (nstream)" 'Successor t = (next t).

(* Basic properties on push *************************************************)

lemma push_at_O: ∀t. @⦃0, ↑t⦄ ≡ 0.
// qed.

lemma push_at_S: ∀t,i1,i2. @⦃i1, t⦄ ≡ i2 → @⦃⫯i1, ↑t⦄ ≡ ⫯i2.
/2 width=1 by at_S1/ qed.

(* Basic inversion lemmas on push *******************************************)

lemma push_inv_at_S: ∀t,i1,i2. @⦃⫯i1, ↑t⦄ ≡ ⫯i2 → @⦃i1, t⦄ ≡ i2.
/2 width=1 by at_inv_SOS/ qed-.

lemma injective_push: injective ? ? push.
#t1 #t2 normalize #H destruct //
qed-.

(* Basic properties on next *************************************************)

lemma next_at: ∀t,i1,i2. @⦃i1, t⦄ ≡ i2 → @⦃i1, ⫯t⦄ ≡ ⫯i2.
* /2 width=1 by at_lift/
qed.

(* Basic inversion lemmas on next *******************************************)

lemma next_inv_at: ∀t,i1,i2. @⦃i1, ⫯t⦄ ≡ ⫯i2 → @⦃i1, t⦄ ≡ i2.
* /2 width=1 by at_inv_xSS/
qed-.

lemma injective_next: injective ? ? next.
* #a1 #t1 * #a2 #t2 normalize #H destruct //
qed-.
