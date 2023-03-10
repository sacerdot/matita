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

rec definition lift_rmap (f) (p) on p: tr_map ā
match p with
[ list_empty     ā f
| list_lcons l q ā š ¢[lift_rmap f q]l
].

interpretation
  "lift (relocation map)"
  'RightTriangleArrow f p = (lift_rmap f p).

(* Basic constructions ******************************************************)

lemma lift_rmap_empty (f):
      f = š ¢[f]š.
// qed.

lemma lift_rmap_rcons (f) (p) (l):
      š ¢[š ¢[f]p]l = š ¢[f](pāl).
// qed.

lemma lift_rmap_d_dx (f) (p) (k:pnat):
      ā*[k](š ¢[f]p) = š ¢[f](pāš±k).
// qed.

lemma lift_rmap_m_dx (f) (p):
      š ¢[f]p = š ¢[f](pāšŗ).
// qed.

lemma lift_rmap_L_dx (f) (p):
      (ā«Æš ¢[f]p) = š ¢[f](pāš).
// qed.

lemma lift_rmap_A_dx (f) (p):
      š ¢[f]p = š ¢[f](pāš).
// qed.

lemma lift_rmap_S_dx (f) (p):
      š ¢[f]p = š ¢[f](pāš¦).
// qed.

(* Constructions with path_append *******************************************)

lemma lift_rmap_append (p) (q) (f):
      š ¢[š ¢[f]p]q = š ¢[f](pāq).
#p #q elim q -q //
qed.

(* Constructions with path_lcons ********************************************)

lemma lift_rmap_lcons (f) (p) (l):
      š ¢[š ¢[f]l]p = š ¢[f](lāp).
// qed.

lemma lift_rmap_d_sn (f) (p) (k:pnat):
      š ¢[ā*[k]f]p = š ¢[f](š±kāp).
// qed.

lemma lift_rmap_m_sn (f) (p):
      š ¢[f]p = š ¢[f](šŗāp).
// qed.

lemma lift_rmap_L_sn (f) (p):
      š ¢[ā«Æf]p = š ¢[f](šāp).
// qed.

lemma lift_rmap_A_sn (f) (p):
      š ¢[f]p = š ¢[f](šāp).
// qed.

lemma lift_rmap_S_sn (f) (p):
      š ¢[f]p = š ¢[f](š¦āp).
// qed.
