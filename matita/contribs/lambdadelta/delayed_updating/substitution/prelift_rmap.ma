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
include "ground/relocation/tr_pn.ma".
include "ground/lib/stream_tls.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

definition prelift_rmap (f) (l): tr_map ≝
match l with
[ label_d k ⇒ ⇂*[k]f
| label_m   ⇒ f
| label_L   ⇒ ⫯f
| label_A   ⇒ f
| label_S   ⇒ f
].

interpretation
  "prelift (relocation map)"
  'UpArrow l f = (prelift_rmap f l).

(* Basic constructions ******************************************************)

lemma prelift_rmap_d (f) (k:pnat):
      ⇂*[k]f = ↑[𝗱k]f.
// qed.

lemma prelift_rmap_m (f):
      f = ↑[𝗺]f.
// qed.

lemma prelift_rmap_L (f):
      (⫯f) = ↑[𝗟]f.
// qed.

lemma prelift_rmap_A (f):
      f = ↑[𝗔]f.
// qed.

lemma prelift_rmap_S (f):
      f = ↑[𝗦]f.
// qed.
