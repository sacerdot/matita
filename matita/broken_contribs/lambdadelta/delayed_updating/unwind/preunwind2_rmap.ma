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
include "ground/relocation/fb/fbr_joins.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

definition preunwind2_rmap (l) (f): 𝔽𝔹 ≝
match l with
[ label_d k ⇒ ⮤*[k]f
| label_L   ⇒ (⫯f)
| label_A   ⇒ f
| label_S   ⇒ f
].

interpretation
  "tailed preunwind (relocation map)"
  'BlackRightTriangle l f = (preunwind2_rmap l f).

(* Basic constructions ******************************************************)

(* Note: this is: f • 𝐮❨n❩ = ▶[𝗱k]f *)
lemma preunwind2_rmap_d (f) (k):
      (⮤*[k]f) = ▶[𝗱k]f.
// qed.

lemma preunwind2_rmap_L (f):
      (⫯f) = ▶[𝗟]f.
// qed.

lemma preunwind2_rmap_A (f):
      f = ▶[𝗔]f.
// qed.

lemma preunwind2_rmap_S (f):
      f = ▶[𝗦]f.
// qed.
