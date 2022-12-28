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

include "delayed_updating/unwind_k/unwind2_rmap.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/notation/functions/black_downtriangle_2.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

definition unwind2_path (f) (p): path ≝
match p with
[ list_empty     ⇒ (𝐞)
| list_lcons l q ⇒
  match l with
  [ label_d k ⇒ (⊗q)◖𝗱(▶[f]q＠⧣❨k❩)
  | label_m   ⇒ ⊗p
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
      (⊗p)◖𝗱((▶[f]p)＠⧣❨k❩) = ▼[f](p◖𝗱k).
// qed.

lemma unwind2_path_m_dx (f) (p):
      ⊗p = ▼[f](p◖𝗺).
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
#f * // * [ #k ] #p //
qed.

lemma unwind2_path_structure (f) (p):
      ⊗p = ▼[f]⊗p.
#f #p elim p -p // * [ #k ] #p #IH //
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

lemma unwind2_path_des_structure (f) (q) (p):
      ⊗q = ▼[f]p → ⊗q = ⊗p.
// qed-.

(* Basic inversions *********************************************************)

lemma eq_inv_d_dx_unwind2_path (f) (q) (p) (h):
      q◖𝗱h = ▼[f]p →
      ∃∃r,k. q = ⊗r & h = ▶[f]r＠⧣❨k❩ & r◖𝗱k = p.
#f #q * [| * [ #k ] #p ] #h
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_m_dx #H0
  elim (eq_inv_d_dx_structure … H0)
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_m_dx_unwind2_path (f) (q) (p):
      q◖𝗺 = ▼[f]p → ⊥.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_m_dx_structure … H0)
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_L_dx_unwind2_path (f) (q) (p):
      q◖𝗟 = ▼[f]p →
      ∃∃r1,r2. q = ⊗r1 & ∀g. 𝐞 = ▼[g]r2 & r1●𝗟◗r2 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_L_dx_structure … H0) -H0 #r1 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_A_dx_unwind2_path (f) (q) (p):
      q◖𝗔 = ▼[f]p →
      ∃∃r1,r2. q = ⊗r1 & ∀g. 𝐞 = ▼[g]r2 & r1●𝗔◗r2 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_A_dx_structure … H0) -H0 #r1 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_S_dx_unwind2_path (f) (q) (p):
      q◖𝗦 = ▼[f]p →
      ∃∃r1,r2. q = ⊗r1 & ∀g. 𝐞 = ▼[g]r2 & r1●𝗦◗r2 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_S_dx_structure … H0) -H0 #r1 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.
