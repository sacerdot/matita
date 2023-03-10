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
include "delayed_updating/notation/functions/flat_1.ma".
include "ground/arith/nat_plus.ma".

(* DEPTH FOR PATH ***********************************************************)

rec definition depth (p) on p: nat ā
match p with
[ list_empty     ā š
| list_lcons l q ā
  match l with
  [ label_d k ā depth q
  | label_m   ā depth q
  | label_L   ā ā(depth q)
  | label_A   ā depth q
  | label_S   ā depth q
  ]
].

interpretation
  "depth (path)"
  'Flat p = (depth p).

(* Basic constructions ******************************************************)

lemma depth_empty: š = ā­š.
// qed.

lemma depth_d_dx (p) (k):
      ā­p = ā­(pāš±k).
// qed.

lemma depth_m_dx (p):
      ā­p = ā­(pāšŗ).
// qed.

lemma depth_L_dx (p):
      āā­p = ā­(pāš).
// qed.

lemma depth_A_dx (p):
      ā­p = ā­(pāš).
// qed.

lemma depth_S_dx (p):
      ā­p = ā­(pāš¦).
// qed.

(* Main constructions *******************************************************)

theorem depth_append (p) (q):
        (ā­p)+(ā­q) = ā­(pāq).
#p #q elim q -q //
* [ #k ] #q #IH <list_append_lcons_sn
[ <depth_d_dx <depth_d_dx //
| <depth_m_dx <depth_m_dx //
| <depth_L_dx <depth_L_dx //
| <depth_A_dx <depth_A_dx //
| <depth_S_dx <depth_S_dx //
]
qed.

(* Constructions with path_lcons ********************************************)

lemma depth_d_sn (p) (k):
      ā­p = ā­(š±kāp).
// qed.

lemma depth_m_sn (p):
      ā­p = ā­(šŗāp).
// qed.

lemma depth_L_sn (p):
      āā­p = ā­(šāp).
// qed.

lemma depth_A_sn (p):
      ā­p = ā­(šāp).
// qed.

lemma depth_S_sn (p):
      ā­p = ā­(š¦āp).
// qed.
