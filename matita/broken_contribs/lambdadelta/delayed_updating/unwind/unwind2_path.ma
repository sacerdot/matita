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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/notation/functions/black_downtriangle_2.ma".
include "ground/relocation/fb/fbr_xapp.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

definition unwind2_path (f) (p): ℙ ≝
match p with
[ list_empty     ⇒ (𝐞)
| list_lcons l q ⇒
  match l with
  [ label_d k ⇒ (⊗q)◖𝗱((▶[q]f)＠❨k❩)
  | label_L   ⇒ ⊗p
  | label_A   ⇒ ⊗p
  | label_S   ⇒ ⊗p
  ]
].

interpretation
  "tailed unwind (path)"
  'BlackDownTriangle f p = (unwind2_path f p).

(* Basic constructions ******************************************************)

lemma unwind2_path_empty (f):
      (𝐞) = ▼[f]𝐞.
// qed.

lemma unwind2_path_d_dx (f) (p) (k) :
      (⊗p)◖𝗱((▶[p]f)＠❨k❩) = ▼[f](p◖𝗱k).
// qed.

lemma unwind2_path_L_dx (f) (p):
      (⊗p)◖𝗟 = ▼[f](p◖𝗟).
// qed.

lemma unwind2_path_A_dx (f) (p):
      (⊗p)◖𝗔 = ▼[f](p◖𝗔).
// qed.

lemma unwind2_path_S_dx (f) (p):
      (⊗p)◖𝗦 = ▼[f](p◖𝗦).
// qed.

(* Constructions with structure *********************************************)

lemma structure_unwind2_path (f) (p):
      ⊗p = ⊗▼[f]p.
#f * //
* [ #k ] #p //
qed.

lemma unwind2_path_structure (f) (p):
      ⊗p = ▼[f]⊗p.
#f #p elim p -p //
* [ #k ] #p #IH //
[ <structure_L_dx <unwind2_path_L_dx //
| <structure_A_dx <unwind2_path_A_dx //
| <structure_S_dx <unwind2_path_S_dx //
]
qed.

lemma unwind2_path_root (f) (p):
      ∃∃r. 𝐞 = ⊗r & ⊗p●r = ▼[f]p.
#f * [| * [ #k ] #p ]
/2 width=3 by ex2_intro/
<unwind2_path_d_dx <structure_d_dx
/2 width=3 by ex2_intro/
qed-.

(* Destructions with structure **********************************************)

lemma eq_des_unwind2_path_bi_structure (f1) (f2) (p1) (p2):
      ▼[f1]p1 = ▼[f2]p2 → ⊗p1 = ⊗p2.
// qed-.

lemma eq_des_structure_unwind2_path (f) (q) (p):
      ⊗q = ▼[f]p → ⊗q = ⊗p.
// qed-.

lemma eq_des_unwind2_path_structure (f) (q) (p):
      ▼[f]p = ⊗q → ⊗p = ⊗q.
// qed-.

(* Basic inversions *********************************************************)

lemma eq_inv_empty_unwind2_path (f) (p):
      (𝐞) = ▼[f]p → 𝐞 = p.
#f * [| * [ #k ] #p ] //
[ <unwind2_path_d_dx #H0 destruct
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_d_dx_unwind2_path (f) (q) (p) (h):
      q◖𝗱h = ▼[f]p →
      ∃∃r,k. q = ⊗r & h = (▶[r]f)＠❨k❩ & r◖𝗱k = p.
#f #q * [| * [ #k ] #p ] #h
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_L_dx_unwind2_path (f) (q) (p):
      q◖𝗟 = ▼[f]p →
      ∃∃r. q = ⊗r & r◖𝗟 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_L_dx #H0 destruct
  /2 width=3 by ex2_intro/
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_A_dx_unwind2_path (f) (q) (p):
      q◖𝗔 = ▼[f]p →
      ∃∃r. q = ⊗r & r◖𝗔 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
  /2 width=3 by ex2_intro/
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_S_dx_unwind2_path (f) (q) (p):
      q◖𝗦 = ▼[f]p →
      ∃∃r. q = ⊗r & r◖𝗦 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
  /2 width=3 by ex2_intro/
]
qed-.
