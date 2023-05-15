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

(* LIFT FOR RELOCATION MAP **************************************************)

rec definition lift_rmap (f) (p) on p: tr_map ≝
match p with
[ list_empty     ⇒ f
| list_lcons l q ⇒ 🠢[lift_rmap f q]l
].

interpretation
  "lift (relocation map)"
  'RightTriangleArrow f p = (lift_rmap f p).

(* Basic constructions ******************************************************)

lemma lift_rmap_empty (f):
      f = 🠢[f]𝐞.
// qed.

lemma lift_rmap_rcons (f) (p) (l):
      🠢[🠢[f]p]l = 🠢[f](p◖l).
// qed.

lemma lift_rmap_d_dx (f) (p) (k:ℤ⁺):
      ⇂*[k](🠢[f]p) = 🠢[f](p◖𝗱k).
// qed.

lemma lift_rmap_m_dx (f) (p):
      🠢[f]p = 🠢[f](p◖𝗺).
// qed.

lemma lift_rmap_L_dx (f) (p):
      (⫯🠢[f]p) = 🠢[f](p◖𝗟).
// qed.

lemma lift_rmap_A_dx (f) (p):
      🠢[f]p = 🠢[f](p◖𝗔).
// qed.

lemma lift_rmap_S_dx (f) (p):
      🠢[f]p = 🠢[f](p◖𝗦).
// qed.

(* Constructions with path_append *******************************************)

lemma lift_rmap_append (p) (q) (f):
      🠢[🠢[f]p]q = 🠢[f](p●q).
#p #q elim q -q //
qed.

(* Constructions with path_lcons ********************************************)

lemma lift_rmap_lcons (f) (p) (l):
      🠢[🠢[f]l]p = 🠢[f](l◗p).
// qed.

lemma lift_rmap_d_sn (f) (p) (k:ℤ⁺):
      🠢[⇂*[k]f]p = 🠢[f](𝗱k◗p).
// qed.

lemma lift_rmap_m_sn (f) (p):
      🠢[f]p = 🠢[f](𝗺◗p).
// qed.

lemma lift_rmap_L_sn (f) (p):
      🠢[⫯f]p = 🠢[f](𝗟◗p).
// qed.

lemma lift_rmap_A_sn (f) (p):
      🠢[f]p = 🠢[f](𝗔◗p).
// qed.

lemma lift_rmap_S_sn (f) (p):
      🠢[f]p = 🠢[f](𝗦◗p).
// qed.
