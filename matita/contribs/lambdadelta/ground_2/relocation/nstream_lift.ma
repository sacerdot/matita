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

definition push: rtmap → rtmap ≝ λf. 0@f.

interpretation "push (nstream)" 'Lift f = (push f).

definition next: rtmap → rtmap.
* #a #f @(⫯a@f)
qed.

interpretation "next (nstream)" 'Successor f = (next f).

(* Basic properties on push *************************************************)

lemma push_at_O: ∀f. @⦃0, ↑f⦄ ≡ 0.
// qed.

lemma push_at_S: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → @⦃⫯i1, ↑f⦄ ≡ ⫯i2.
/2 width=1 by at_S1/ qed.

(* Basic inversion lemmas on push *******************************************)

lemma push_inv_at_S: ∀f,i1,i2. @⦃⫯i1, ↑f⦄ ≡ ⫯i2 → @⦃i1, f⦄ ≡ i2.
/2 width=1 by at_inv_SOS/ qed-.

lemma injective_push: injective ? ? push.
#f1 #f2 normalize #H destruct //
qed-.

lemma discr_push_next: ∀f1,f2. ↑f1 = ⫯f2 → ⊥.
#f1 * #n2 #f2 normalize #H destruct
qed-.

lemma discr_next_push: ∀f1,f2. ⫯f1 = ↑f2 → ⊥.
* #n1 #f1 #f2 normalize #H destruct
qed-.

(* Basic properties on next *************************************************)

lemma next_at: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → @⦃i1, ⫯f⦄ ≡ ⫯i2.
* /2 width=1 by at_lift/
qed.

(* Basic inversion lemmas on next *******************************************)

lemma next_inv_at: ∀f,i1,i2. @⦃i1, ⫯f⦄ ≡ ⫯i2 → @⦃i1, f⦄ ≡ i2.
* /2 width=1 by at_inv_xSS/
qed-.

lemma injective_next: injective ? ? next.
* #a1 #f1 * #a2 #f2 normalize #H destruct //
qed-.
