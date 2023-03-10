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

include "ground/arith/nat_plus.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/sharp_1.ma".

(* HEIGHT FOR PATH **********************************************************)

rec definition height (p) on p: nat ā
match p with
[ list_empty     ā š
| list_lcons l q ā
  match l with
  [ label_d k ā height q + k
  | label_m   ā height q
  | label_L   ā height q
  | label_A   ā height q
  | label_S   ā height q
  ]
].

interpretation
  "height (path)"
  'Sharp p = (height p).

(* Basic constructions ******************************************************)

lemma height_empty: š = āÆš.
// qed.

lemma height_d_dx (p) (k:pnat):
      (āÆp)+k = āÆ(pāš±k).
// qed.

lemma height_m_dx (p):
      (āÆp) = āÆ(pāšŗ).
// qed.

lemma height_L_dx (p):
      (āÆp) = āÆ(pāš).
// qed.

lemma height_A_dx (p):
      (āÆp) = āÆ(pāš).
// qed.

lemma height_S_dx (p):
      (āÆp) = āÆ(pāš¦).
// qed.

(* Main constructions *******************************************************)

theorem height_append (p) (q):
        (āÆp+āÆq) = āÆ(pāq).
#p #q elim q -q //
* [ #k ] #q #IH <list_append_lcons_sn
[ <height_d_dx <height_d_dx //
| <height_m_dx <height_m_dx //
| <height_L_dx <height_L_dx //
| <height_A_dx <height_A_dx //
| <height_S_dx <height_S_dx //
]
qed.

(* Constructions with path_lcons ********************************************)

lemma height_d_sn (p) (k:pnat):
      k+āÆp = āÆ(š±kāp).
// qed.

lemma height_m_sn (p):
      āÆp = āÆ(šŗāp).
// qed.

lemma height_L_sn (p):
      āÆp = āÆ(šāp).
// qed.

lemma height_A_sn (p):
      āÆp = āÆ(šāp).
// qed.

lemma height_S_sn (p):
      āÆp = āÆ(š¦āp).
// qed.
