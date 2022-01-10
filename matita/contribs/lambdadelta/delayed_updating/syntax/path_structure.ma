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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/circled_times_1.ma".

(* STRUCTURE FOR PATH *******************************************************)

rec definition structure (p) on p ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒
   match l with
   [ label_node_d n ⇒ structure q
   | label_edge_L   ⇒ 𝗟◗structure q
   | label_edge_A   ⇒ 𝗔◗structure q
   | label_edge_S   ⇒ 𝗦◗structure q
   ]
].

interpretation
  "structure (path)"
  'CircledTimes p = (structure p).

(* Basic constructions ******************************************************)

lemma structure_empty:
      𝐞 = ⊗𝐞.
// qed.

lemma structure_d_sn (p) (n):
      ⊗p = ⊗(𝗱n◗p).
// qed.

lemma structure_L_sn (p):
      𝗟◗⊗p = ⊗(𝗟◗p).
// qed.

lemma structure_A_sn (p):
      𝗔◗⊗p = ⊗(𝗔◗p).
// qed.

lemma structure_S_sn (p):
      𝗦◗⊗p = ⊗(𝗦◗p).
// qed.

(* Main constructions *******************************************************)

theorem structure_idem (p):
        ⊗p = ⊗⊗p.
#p elim p -p [| * [ #n ] #p #IH ] //
qed.

theorem structure_append (p1) (p2):
        ⊗p1●⊗p2 = ⊗(p1●p2).
#p1 elim p1 -p1 [| * [ #n ] #p1 #IH ] #p2
[||*: <list_append_lcons_sn ] //
qed.

(* Constructions with list_rcons ********************************************)

lemma structure_d_dx (p) (n):
      ⊗p = ⊗(p◖𝗱n).
#p #n <structure_append //
qed.

lemma structure_L_dx (p):
      (⊗p)◖𝗟 = ⊗(p◖𝗟).
#p <structure_append //
qed.

lemma structure_A_dx (p):
      (⊗p)◖𝗔 = ⊗(p◖𝗔).
#p <structure_append //
qed.

lemma structure_S_dx (p):
      (⊗p)◖𝗦 = ⊗(p◖𝗦).
#p <structure_append //
qed.
