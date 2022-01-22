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
include "ground/notation/functions/verticalbars_1.ma".

(* DEPTH FOR PATH ***********************************************************)

rec definition depth (p) on p: pnat ≝
match p with
[ list_empty     ⇒ 𝟏
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

lemma depth_empty: 𝟏 = ❘𝐞❘.
// qed.

lemma depth_d (q) (n): ❘q❘ = ❘𝗱n◗q❘.
// qed.

lemma depth_m (q): ❘q❘ = ❘𝗺◗q❘.
// qed.

lemma depth_L (q): ↑❘q❘ = ❘𝗟◗q❘.
// qed.

lemma depth_A (q): ❘q❘ = ❘𝗔◗q❘.
// qed.

lemma depth_S (q): ❘q❘ = ❘𝗦◗q❘.
// qed.
