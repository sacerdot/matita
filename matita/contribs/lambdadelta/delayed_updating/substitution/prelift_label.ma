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

include "delayed_updating/notation/functions/uparrow_2.ma".
include "delayed_updating/syntax/label.ma".
include "ground/relocation/tr_pap.ma".

(* PRELIFT FOR LABEL ********************************************************)

definition prelift_label (f) (l): label ≝
match l with
[ label_d n ⇒ 𝗱(f＠⧣❨n❩)
| label_m   ⇒ 𝗺
| label_L   ⇒ 𝗟
| label_A   ⇒ 𝗔
| label_S   ⇒ 𝗦
].

interpretation
  "prelift (label)"
  'UpArrow f l = (prelift_label f l).

(* Basic constructions ******************************************************)

lemma prelift_label_d (f) (n):
      (𝗱(f＠⧣❨n❩)) = ↑[f]𝗱n.
// qed.

lemma prelift_label_m (f):
      (𝗺) = ↑[f]𝗺.
// qed.

lemma prelift_label_L (f):
      (𝗟) = ↑[f]𝗟.
// qed.

lemma prelift_label_A (f):
      (𝗔) = ↑[f]𝗔.
// qed.

lemma prelift_label_S (f):
      (𝗦) = ↑[f]𝗦.
// qed.
