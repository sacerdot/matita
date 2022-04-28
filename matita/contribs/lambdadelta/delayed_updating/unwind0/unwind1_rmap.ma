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

include "delayed_updating/substitution/lift_length.ma".
include "delayed_updating/notation/functions/black_righttriangle_1.ma".
include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_compose.ma".

(* BASIC UNWIND FOR RELOCATION MAP ******************************************)

rec definition unwind1_rmap_pnat (n) (p) on n ≝
match n with
[ punit   ⇒ 𝐢
| psucc m ⇒
  match p with
  [ list_empty     ⇒ 𝐢
  | list_lcons l q ⇒
    match l with
    [ label_d n ⇒ (unwind1_rmap_pnat m (↑[𝐮❨n❩]q))∘(↑[q]𝐮❨n❩)
    | label_m   ⇒ unwind1_rmap_pnat m q
    | label_L   ⇒ unwind1_rmap_pnat m q
    | label_A   ⇒ unwind1_rmap_pnat m q
    | label_S   ⇒ unwind1_rmap_pnat m q
    ]
  ]
].

definition unwind1_rmap (p) ≝
           unwind1_rmap_pnat (↑❘p❘) p.

interpretation
  "basic unwind (relocation map)"
  'BlackRightTriangle p = (unwind1_rmap p).

(* Basic constructions ******************************************************)

lemma unwind1_rmap_unfold (p):
      unwind1_rmap_pnat (↑❘p❘) p = ▶p.
// qed-.

lemma unwind1_rmap_empty:
      (𝐢) = ▶(𝐞).
// qed.

lemma unwind1_rmap_d_sn (p) (n:pnat):
      (▶(↑[𝐮❨n❩]p))∘(↑[p]𝐮❨n❩) = ▶(𝗱n◗p).
#p #n
<unwind1_rmap_unfold <lift_path_length //
qed.

lemma unwind1_rmap_m_sn (p):
      ▶p = ▶(𝗺◗p).
// qed.

lemma unwind1_rmap_L_sn (p):
      ▶p = ▶(𝗟◗p).
// qed.

lemma unwind1_rmap_A_sn (p):
      ▶p = ▶(𝗔◗p).
// qed.

lemma unwind1_rmap_S_sn (p):
      ▶p = ▶(𝗦◗p).
// qed.
