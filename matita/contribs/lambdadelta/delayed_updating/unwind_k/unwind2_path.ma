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

definition unwind2_path (f) (p): path â
match p with
[ list_empty     â (ğ)
| list_lcons l q â
  match l with
  [ label_d k â (âq)âğ±(â¶[f]qï¼ â§£â¨kâ©)
  | label_m   â âp
  | label_L   â âp
  | label_A   â âp
  | label_S   â âp
  ]
].

interpretation
  "tailed unwind (path)"
  'BlackDownTriangle f p = (unwind2_path f p).

(* Basic constructions ******************************************************)

lemma unwind2_path_empty (f):
      (ğ) = â¼[f]ğ.
// qed.

lemma unwind2_path_d_dx (f) (p) (k) :
      (âp)âğ±((â¶[f]p)ï¼ â§£â¨kâ©) = â¼[f](pâğ±k).
// qed.

lemma unwind2_path_m_dx (f) (p):
      âp = â¼[f](pâğº).
// qed.

lemma unwind2_path_L_dx (f) (p):
      (âp)âğ = â¼[f](pâğ).
// qed.

lemma unwind2_path_A_dx (f) (p):
      (âp)âğ = â¼[f](pâğ).
// qed.

lemma unwind2_path_S_dx (f) (p):
      (âp)âğ¦ = â¼[f](pâğ¦).
// qed.

(* Constructions with structure *********************************************)

lemma structure_unwind2_path (f) (p):
      âp = ââ¼[f]p.
#f * // * [ #k ] #p //
qed.

lemma unwind2_path_structure (f) (p):
      âp = â¼[f]âp.
#f #p elim p -p // * [ #k ] #p #IH //
[ <structure_L_dx <unwind2_path_L_dx //
| <structure_A_dx <unwind2_path_A_dx //
| <structure_S_dx <unwind2_path_S_dx //
]
qed.

lemma unwind2_path_root (f) (p):
      ââr. ğ = âr & âpâr = â¼[f]p.
#f * [| * [ #k ] #p ]
/2 width=3 by ex2_intro/
<unwind2_path_d_dx <structure_d_dx
/2 width=3 by ex2_intro/
qed-.

(* Destructions with structure **********************************************)

lemma unwind2_path_des_structure (f) (q) (p):
      âq = â¼[f]p â âq = âp.
// qed-.

(* Basic inversions *********************************************************)

lemma eq_inv_d_dx_unwind2_path (f) (q) (p) (h):
      qâğ±h = â¼[f]p â
      ââr,k. q = âr & h = â¶[f]rï¼ â§£â¨kâ© & râğ±k = p.
#f #q * [| * [ #k ] #p ] #h
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_m_dx #H0
  elim (eq_inv_d_dx_structure â¦ H0)
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_m_dx_unwind2_path (f) (q) (p):
      qâğº = â¼[f]p â â¥.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_m_dx_structure â¦ H0)
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_L_dx_unwind2_path (f) (q) (p):
      qâğ = â¼[f]p â
      ââr1,r2. q = âr1 & âg. ğ = â¼[g]r2 & r1âğâr2 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_L_dx_structure â¦ H0) -H0 #r1 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_A_dx_unwind2_path (f) (q) (p):
      qâğ = â¼[f]p â
      ââr1,r2. q = âr1 & âg. ğ = â¼[g]r2 & r1âğâr2 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_A_dx_structure â¦ H0) -H0 #r1 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_S_dx #H0 destruct
]
qed-.

lemma eq_inv_S_dx_unwind2_path (f) (q) (p):
      qâğ¦ = â¼[f]p â
      ââr1,r2. q = âr1 & âg. ğ = â¼[g]r2 & r1âğ¦âr2 = p.
#f #q * [| * [ #k ] #p ]
[ <unwind2_path_empty #H0 destruct
| <unwind2_path_d_dx #H0 destruct
| <unwind2_path_m_dx #H0
  elim (eq_inv_S_dx_structure â¦ H0) -H0 #r1 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <unwind2_path_L_dx #H0 destruct
| <unwind2_path_A_dx #H0 destruct
| <unwind2_path_S_dx #H0 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.
