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

include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_inner.ma".
include "ground/xoa/ex_4_2.ma".

(* STRUCTURE FOR PATH *******************************************************)

(* Constructions with pic ***************************************************)

lemma path_split_pic_sn (r):
      ∃∃p,q. p ϵ 𝐈 & 𝐞 = ⊗q & p●q = r.
#r elim r -r [| * [ #k ] #r * #p #q #Hp #Hq #H0 ] destruct
[ /2 width=5 by pic_empty, ex3_2_intro/
| /2 width=5 by ex3_2_intro/
| @(ex3_2_intro … (p●q◖𝗟) (𝐞)) //
| @(ex3_2_intro … (p●q◖𝗔) (𝐞)) //
| @(ex3_2_intro … (p●q◖𝗦) (𝐞)) //
]
qed-.

lemma structure_pic (p):
      ⊗p ϵ 𝐈.
#p elim p -p
[ <structure_empty //
| * [ #k ] #p #IH
  [ <structure_d_dx //
  | <structure_L_dx //
  | <structure_A_dx //
  | <structure_S_dx //
  ]
]
qed.

(* Inversions with pic ******************************************************)

lemma eq_inv_empty_structure_pic (p):
      p ϵ 𝐈 → 𝐞 = ⊗p → 𝐞 = p.
#p * -p // #p
[ <structure_L_dx
| <structure_A_dx
| <structure_S_dx
] #H0 destruct
qed-.

(* Main inversions with pic *************************************************)

theorem eq_inv_append_structure_pic (p) (q) (r):
        p●q = ⊗r →
        ∃∃r1,r2. r1 ϵ 𝐈 & p = ⊗r1 & q = ⊗r2 & r1●r2 = r.
#p #q #r #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
elim (path_split_pic_sn r1) #p1 #q1 #Hp1 #Hq1 #H0 destruct
<structure_append <list_append_assoc
@(ex4_2_intro … p1 (q1●r2)) //
<structure_append //
qed-.
