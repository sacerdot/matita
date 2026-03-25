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

include "delayed_updating/syntax/label.ma".
include "delayed_updating/notation/functions/circled_zero_1.ma".

(* CLEAR FOR LABELS *********************************************************)

definition label_clear (l) ≝ 
match l with
[ label_d k ⇒ 𝗱(𝟎)
| label_L   ⇒ 𝗟
| label_A   ⇒ 𝗔
| label_S   ⇒ 𝗦
].

interpretation
  "clear (label)"
  'CircledZero l = (label_clear l).

(* Basic constructions ******************************************************)

lemma label_clear_d (k):
      (𝗱𝟎) = ⓪𝗱k.
//
qed.

lemma label_clear_L:
      (𝗟) = ⓪𝗟.
//
qed.

lemma label_clear_A:
      (𝗔) = ⓪𝗔.
//
qed.

lemma label_clear_S:
      (𝗦) = ⓪𝗦.
//
qed.
