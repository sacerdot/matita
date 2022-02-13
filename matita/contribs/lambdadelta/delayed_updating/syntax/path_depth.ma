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
include "ground/arith/nat_plus.ma".
include "ground/notation/functions/verticalbars_1.ma".

(* DEPTH FOR PATH ***********************************************************)

rec definition depth (p) on p: nat ≝
match p with
[ list_empty     ⇒ 𝟎
| list_lcons l q ⇒
  match l with
  [ label_d _ ⇒ depth q
  | label_m   ⇒ depth q
  | label_L   ⇒ ↑(depth q)
  | label_A   ⇒ depth q
  | label_S   ⇒ depth q
  ]
].

interpretation
  "depth (path)"
  'VerticalBars p = (depth p).

(* Basic constructions ******************************************************)

lemma depth_empty: 𝟎 = ❘𝐞❘.
// qed.

lemma depth_d_sn (q) (n): ❘q❘ = ❘𝗱n◗q❘.
// qed.

lemma depth_m_sn (q): ❘q❘ = ❘𝗺◗q❘.
// qed.

lemma depth_L_sn (q): ↑❘q❘ = ❘𝗟◗q❘.
// qed.

lemma depth_A_sn (q): ❘q❘ = ❘𝗔◗q❘.
// qed.

lemma depth_S_sn (q): ❘q❘ = ❘𝗦◗q❘.
// qed.

(* Advanced constructions with nplus ****************************************)

lemma depth_plus (p1) (p2):
      ❘p2❘+❘p1❘ = ❘p1●p2❘.
#p1 elim p1 -p1 //
* [ #n ] #p1 #IH #p2 <list_append_lcons_sn
[ <depth_d_sn <depth_d_sn //
| <depth_m_sn <depth_m_sn //
| <depth_L_sn <depth_L_sn //
| <depth_A_sn <depth_A_sn //
| <depth_S_sn <depth_S_sn //
]
qed.
