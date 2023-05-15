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
include "delayed_updating/notation/functions/black_righttriangle_2.ma".
include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_compose.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

definition preunwind2_rmap (f) (l): tr_map ≝
match l with
[ label_d k ⇒ f∘𝐮❨k❩
| label_m   ⇒ f
| label_L   ⇒ ⫯f
| label_A   ⇒ f
| label_S   ⇒ f
].

interpretation
  "tailed preunwind (relocation map)"
  'BlackRightTriangle f l = (preunwind2_rmap f l).

(* Basic constructions ******************************************************)

lemma preunwind2_rmap_d (f) (k:ℤ⁺):
      f∘𝐮❨k❩ = ▶[f]𝗱k.
// qed.

lemma preunwind2_rmap_m (f):
      f = ▶[f]𝗺.
// qed.

lemma preunwind2_rmap_L (f):
      (⫯f) = ▶[f]𝗟.
// qed.

lemma preunwind2_rmap_A (f):
      f = ▶[f]𝗔.
// qed.

lemma preunwind2_rmap_S (f):
      f = ▶[f]𝗦.
// qed.
