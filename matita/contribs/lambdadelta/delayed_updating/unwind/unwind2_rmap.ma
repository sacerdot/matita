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
include "delayed_updating/notation/functions/black_righttriangle_2.ma".
include "delayed_updating/notation/functions/black_righttriangle_1.ma".
include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_compose.ma".

(* UNWIND MAP FOR PATH ******************************************************)

rec definition unwind2_rmap (f) (p) on p: tr_map ≝
match p with
[ list_empty     ⇒ f
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒ (unwind2_rmap f q)∘𝐮❨n❩
  | label_m   ⇒ unwind2_rmap f q
  | label_L   ⇒ ⫯(unwind2_rmap f q)
  | label_A   ⇒ unwind2_rmap f q
  | label_S   ⇒ unwind2_rmap f q
  ]
].

interpretation
  "tailed unwind map (reversed path)"
  'BlackRightTriangle f p = (unwind2_rmap f p).

interpretation
  "unwind map (reversed path)"
  'BlackRightTriangle p = (unwind2_rmap tr_id p).

(* Basic constructions ******************************************************)

lemma unwind2_rmap_empty (f):
      f = ▶[f]𝐞.
// qed.

lemma unwind2_rmap_d_sn (f) (p) (n:pnat):
      (▶[f]p∘𝐮❨n❩) = ▶[f](𝗱n◗p).
// qed.

lemma unwind2_rmap_m_sn (f) (p):
      ▶[f]p = ▶[f](𝗺◗p).
// qed.

lemma unwind2_rmap_L_sn (f) (p):
      (⫯▶[f]p) = ▶[f](𝗟◗p).
// qed.

lemma unwind2_rmap_A_sn (f) (p):
      ▶[f]p = ▶[f](𝗔◗p).
// qed.

lemma unwind2_rmap_S_sn (f) (p):
      ▶[f]p = ▶[f](𝗦◗p).
// qed.

(* Constructions with list_append *******************************************)

lemma unwind2_rmap_append (f) (p1) (p2):
      ▶[▶[f]p2]p1 = ▶[f](p1●p2).
#f #p1 elim p1 -p1 //
* [ #n ] #p1 #IH #p2 //
[ <unwind2_rmap_m_sn <unwind2_rmap_m_sn //
| <unwind2_rmap_L_sn <unwind2_rmap_L_sn //
| <unwind2_rmap_A_sn <unwind2_rmap_A_sn //
| <unwind2_rmap_S_sn <unwind2_rmap_S_sn //
]
qed.

(* Constructions with list_rcons ********************************************)

lemma unwind2_rmap_d_dx (f) (p) (n:pnat):
      ▶[f∘𝐮❨n❩]p = ▶[f](p◖𝗱n).
// qed.

lemma unwind2_rmap_m_dx (f) (p):
      ▶[f]p = ▶[f](p◖𝗺).
// qed.

lemma unwind2_rmap_L_dx (f) (p):
      ▶[⫯f]p = ▶[f](p◖𝗟).
// qed.

lemma unwind2_rmap_A_dx (f) (p):
      ▶[f]p = ▶[f](p◖𝗔).
// qed.

lemma unwind2_rmap_S_dx (f) (p):
      ▶[f]p = ▶[f](p◖𝗦).
// qed.
