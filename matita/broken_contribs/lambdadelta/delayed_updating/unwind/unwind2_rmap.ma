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

include "delayed_updating/unwind/preunwind2_rmap.ma".
include "delayed_updating/syntax/path.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

rec definition unwind2_rmap (p) (f) on p: 𝔽𝔹 ≝
match p with
[ list_empty     ⇒ f
| list_lcons l q ⇒ ▶[l](unwind2_rmap q f)
].

interpretation
  "tailed unwind (relocation map)"
  'BlackRightTriangle p f = (unwind2_rmap p f).

(* Basic constructions ******************************************************)

lemma unwind2_rmap_empty (f):
      f = ▶[𝐞]f.
// qed.

lemma unwind2_rmap_rcons (f) (p) (l):
      ▶[l]▶[p]f = ▶[p◖l]f.
// qed.

(* Note: this is: ▶[p]f • 𝐮❨k❩ = ▶[p◖𝗱k]f *)
lemma unwind2_rmap_d_dx (f) (p) (k):
      (⮤*[k]▶[p]f) = ▶[p◖𝗱k]f.
// qed.

lemma unwind2_rmap_L_dx (f) (p):
      (⫯▶[p]f) = ▶[p◖𝗟]f.
// qed.

lemma unwind2_rmap_A_dx (f) (p):
      ▶[p]f = ▶[p◖𝗔]f.
// qed.

lemma unwind2_rmap_S_dx (f) (p):
      ▶[p]f = ▶[p◖𝗦]f.
// qed.

(* Constructions with path_append *******************************************)

lemma unwind2_rmap_append (f) (p) (q):
      ▶[q]▶[p]f = ▶[p●q]f.
#f #p #q elim q -q // #l #q #IH
<unwind2_rmap_rcons <unwind2_rmap_rcons //
qed.

(* Constructions with path_lcons ********************************************)

lemma unwind2_rmap_lcons (f) (p) (l):
      ▶[p]▶[l]f = ▶[l◗p]f.
// qed.

lemma unwind2_rmap_d_sx (f) (p) (k):
      ▶[p]⮤*[k]f = ▶[𝗱k◗p]f.
// qed.

lemma unwind2_rmap_L_sx (f) (p):
      ▶[p]⫯f = ▶[𝗟◗p]f.
// qed.

lemma unwind2_rmap_A_sx (f) (p):
      ▶[p]f = ▶[𝗔◗p]f.
// qed.

lemma unwind2_rmap_S_sx (f) (p):
      ▶[p]f = ▶[𝗦◗p]f.
// qed.
