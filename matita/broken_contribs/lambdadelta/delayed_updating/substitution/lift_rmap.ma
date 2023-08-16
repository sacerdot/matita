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

include "delayed_updating/substitution/prelift_rmap.ma".
include "delayed_updating/syntax/path.ma".
include "ground/relocation/fb/fbr_ctls_plus.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

rec definition lift_rmap (p) (f) on p: 𝔽𝔹 ≝
match p with
[ list_empty     ⇒ f
| list_lcons l q ⇒ 🠢[l](lift_rmap q f)
].

interpretation
  "lift (relocation map)"
  'RightTriangleArrow p f = (lift_rmap p f).

(* Basic constructions ******************************************************)

lemma lift_rmap_empty (f):
      f = 🠢[𝐞]f.
// qed.

lemma lift_rmap_rcons (f) (p) (l):
      (🠢[l]🠢[p]f) = 🠢[p◖l]f.
// qed.

lemma lift_rmap_d_dx (f) (p) (k):
      (⫰*[k]🠢[p]f) = 🠢[p◖𝗱k]f.
// qed.

lemma lift_rmap_m_dx (f) (p):
      (🠢[p]f) = 🠢[p◖𝗺]f.
// qed.

lemma lift_rmap_L_dx (f) (p):
      (⫯🠢[p]f) = 🠢[p◖𝗟]f.
// qed.

lemma lift_rmap_A_dx (f) (p):
      (🠢[p]f) = 🠢[p◖𝗔]f.
// qed.

lemma lift_rmap_S_dx (f) (p):
      (🠢[p]f) = 🠢[p◖𝗦]f.
// qed.

(* Constructions with path_append *******************************************)

lemma lift_rmap_append (p) (q) (f):
      (🠢[q]🠢[p]f) = 🠢[p●q]f.
#p #q elim q -q //
qed.

(* Constructions with path_lcons ********************************************)

lemma lift_rmap_lcons (f) (p) (l):
      (🠢[p]🠢[l]f) = 🠢[l◗p]f.
// qed.

lemma lift_rmap_d_sn (f) (p) (k):
      (🠢[p]⫰*[k]f) = 🠢[𝗱k◗p]f.
// qed.

lemma lift_rmap_m_sn (f) (p):
      (🠢[p]f) = 🠢[𝗺◗p]f.
// qed.

lemma lift_rmap_L_sn (f) (p):
      (🠢[p]⫯f) = 🠢[𝗟◗p]f.
// qed.

lemma lift_rmap_A_sn (f) (p):
      (🠢[p]f) = 🠢[𝗔◗p]f.
// qed.

lemma lift_rmap_S_sn (f) (p):
      (🠢[p]f) = 🠢[𝗦◗p]f.
// qed.

(* Advanced constructions ***************************************************)

lemma ctls_lift_rmap_d_dx (f) (p) (n) (k):
      (⫰*[n+k]🠢[p]f) = ⫰*[n]🠢[p◖𝗱k]f.
#f #p #n #k
<nplus_comm <fbr_ctls_plus //
qed.

(* TODO
lemma lift_rmap_unfold_d_dx (f) (p) (k) (h):
      (🠢[p]f)＠⧣❨h+k❩-(🠢[p]f)＠⧣❨k❩ = (🠢[p◖𝗱k]f)＠⧣❨h❩.
// qed.
*)
