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
| list_lcons l q ⇒ ↑[l](lift_rmap f q)
].

interpretation
  "lift (relocation map)"
  'UpArrow p f = (lift_rmap f p).

(* Basic constructions ******************************************************)

lemma lift_rmap_empty (f):
      f = ↑[𝐞]f.
// qed.

lemma lift_rmap_rcons (f) (p) (l):
      ↑[l]↑[p]f = ↑[p◖l]f.
// qed.

lemma lift_rmap_d_dx (f) (p) (k:pnat):
      ⇂*[k](↑[p]f) = ↑[p◖𝗱k]f.
// qed.

lemma lift_rmap_m_dx (f) (p):
      ↑[p]f = ↑[p◖𝗺]f.
// qed.

lemma lift_rmap_L_dx (f) (p):
      (⫯↑[p]f) = ↑[p◖𝗟]f.
// qed.

lemma lift_rmap_A_dx (f) (p):
      ↑[p]f = ↑[p◖𝗔]f.
// qed.

lemma lift_rmap_S_dx (f) (p):
      ↑[p]f = ↑[p◖𝗦]f.
// qed.

(* Constructions with path_append *******************************************)

lemma lift_rmap_append (p) (q) (f):
      ↑[q]↑[p]f = ↑[p●q]f.
#p #q elim q -q //
qed.

(* Constructions with path_lcons ********************************************)

lemma lift_rmap_lcons (f) (p) (l):
      ↑[p]↑[l]f = ↑[l◗p]f.
// qed.

lemma lift_rmap_d_sn (f) (p) (k:pnat):
      ↑[p](⇂*[k]f) = ↑[𝗱k◗p]f.
// qed.

lemma lift_rmap_m_sn (f) (p):
      ↑[p]f = ↑[𝗺◗p]f.
// qed.

lemma lift_rmap_L_sn (f) (p):
      ↑[p](⫯f) = ↑[𝗟◗p]f.
// qed.

lemma lift_rmap_A_sn (f) (p):
      ↑[p]f = ↑[𝗔◗p]f.
// qed.

lemma lift_rmap_S_sn (f) (p):
      ↑[p]f = ↑[𝗦◗p]f.
// qed.
