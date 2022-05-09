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
include "delayed_updating/notation/functions/black_righttriangle_1.ma".
include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_compose.ma".

(* BASIC UNWIND MAP FOR PATH ************************************************)

rec definition unwind1_rmap p on p: tr_map ≝
match p with
[ list_empty     ⇒ 𝐢
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒ (unwind1_rmap q)∘𝐮❨n❩
  | label_m   ⇒ unwind1_rmap q
  | label_L   ⇒ ⫯(unwind1_rmap q)
  | label_A   ⇒ unwind1_rmap q
  | label_S   ⇒ unwind1_rmap q
  ]
].

interpretation
  "basic unwind map (reversed path)"
  'BlackRightTriangle p = (unwind1_rmap p).

(* Basic constructions *******************************************************)

lemma unwind1_rmap_empty:
      (𝐢) = ▶(𝐞).
// qed.

lemma unwind1_rmap_d_sn (p) (n:pnat):
      (▶p∘𝐮❨n❩) = ▶(𝗱n◗p).
// qed.

lemma unwind1_rmap_m_sn (p):
      ▶p = ▶(𝗺◗p).
// qed.

lemma unwind1_rmap_L_sn (p):
      (⫯▶p) = ▶(𝗟◗p).
// qed.

lemma unwind1_rmap_A_sn (p):
      ▶p = ▶(𝗔◗p).
// qed.

lemma unwind1_rmap_S_sn (p):
      ▶p = ▶(𝗦◗p).
// qed.
