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

include "ground/notation/functions/upspoon_1.ma".
include "ground/lib/stream.ma".
include "ground/arith/pnat.ma".

(* RELOCATION P-STREAM ******************************************************)

definition rtmap: Type[0] ≝ stream pnat.

definition push: rtmap → rtmap ≝ λf. 𝟏⨮f.

interpretation "push (pstream)" 'UpSpoon f = (push f).

definition next: rtmap → rtmap.
* #p #f @(↑p⨮f)
defined.

interpretation "next (pstream)" 'UpArrow f = (next f).

(* Basic properties *********************************************************)

lemma push_rew: ∀f. 𝟏⨮f = ⫯f.
// qed.

lemma next_rew: ∀f,p. (↑p)⨮f = ↑(p⨮f).
// qed.

(* Basic inversion lemmas ***************************************************)

lemma injective_push: injective ? ? push.
#f1 #f2 <push_rew <push_rew #H destruct //
qed-.

lemma discr_push_next: ∀f1,f2. ⫯f1 = ↑f2 → ⊥.
#f1 * #p2 #f2 <push_rew <next_rew #H destruct
qed-.

lemma discr_next_push: ∀f1,f2. ↑f1 = ⫯f2 → ⊥.
* #p1 #f1 #f2 <next_rew <push_rew #H destruct
qed-.

lemma injective_next: injective ? ? next.
* #p1 #f1 * #p2 #f2 <next_rew <next_rew #H destruct //
qed-.

lemma push_inv_seq_sn: ∀f,g,p. p⨮g = ⫯f → ∧∧ 𝟏 = p & g = f.
#f #g #p <push_rew #H destruct /2 width=1 by conj/
qed-.

lemma push_inv_seq_dx: ∀f,g,p. ⫯f = p⨮g → ∧∧ 𝟏 = p & g = f.
#f #g #p <push_rew #H destruct /2 width=1 by conj/
qed-.

lemma next_inv_seq_sn: ∀f,g,p. p⨮g = ↑f → ∃∃q. q⨮g = f & ↑q = p.
* #q #f #g #p <next_rew #H destruct /2 width=3 by ex2_intro/
qed-.

lemma next_inv_seq_dx: ∀f,g,p. ↑f = p⨮g → ∃∃q. q⨮g = f & ↑q = p.
* #q #f #g #p <next_rew #H destruct /2 width=3 by ex2_intro/
qed-.

lemma case_prop (Q:predicate rtmap):
      (∀f. Q (⫯f)) → (∀f. Q (↑f)) → ∀f. Q f.
#Q #H1 #H2 * * //
qed-.

lemma case_type0 (Q:rtmap→Type[0]):
      (∀f. Q (⫯f)) → (∀f. Q (↑f)) → ∀f. Q f.
#Q #H1 #H2 * * //
qed-.

lemma iota_push: ∀Q,a,b,f. a f = case_type0 Q a b (⫯f).
// qed.

lemma iota_next: ∀Q,a,b,f. b f = case_type0 Q a b (↑f).
#Q #a #b * //
qed.
