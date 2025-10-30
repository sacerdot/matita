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

include "delayed_updating/syntax/path_balanced_ind.ma".
include "delayed_updating/syntax/path_structure.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Destructions with path_structure *****************************************)

lemma pbc_des_structure (b):
      b ϵ 𝐁 → b = ⊗b.
#b #Hb elim Hb -b //
[ #b #_ #IH
  <structure_A_sx <structure_L_dx <IH -IH //
| #b1 #b2 #_ #_ #IH1 #IH2
  <structure_append <IH1 <IH2 -IH1 -IH2 //
]
qed-.

lemma path_eq_des_pAb_bi_pbc (p1) (p2) (b1) (b2):
      ⊗b1 ϵ 𝐁 → ⊗b2 ϵ 𝐁 → p1◖𝗔●b1 = p2◖𝗔●b2 → b1 = b2.
#p1 #p2 #b1 #b2 #Hb1 #Hb2 #H0
elim (eq_inv_list_append_bi … H0) -H0 * #x
[ #H0 #Hx destruct
  elim (eq_inv_list_lcons_append ????? Hx) -Hx *
  [ #H0 #_ -Hb1 -Hb2 destruct //
  | #q #H0 #_ -p2 destruct
    <structure_append in Hb1; <structure_A_dx #Hb1
    lapply (pbc_inv_append_dx … Hb1 Hb2) -Hb1 -Hb2 #H0
    elim (pbc_inv_A_dx … H0)
  ]
| #Hq #H0 destruct
  elim (eq_inv_list_lcons_append ????? Hq) -Hq *
  [ -Hb1 -Hb2 #H1 #_ destruct //
  | #y #H1 #H2 destruct
    <structure_append in Hb2; <structure_A_dx #Hb2
    lapply (pbc_inv_append_dx … Hb2 Hb1) -Hb2 -Hb1 #H0
    elim (pbc_inv_A_dx … H0)
  ]
]
qed-.

(* Inversions with path_structure *******************************************)

axiom path_eq_inv_pbq_pSq_pbc (p2) (p1) (b) (q1) (q2):
      (p1●b)●q1 = p2◖𝗦●q2 → ⊗b ϵ 𝐁 →
      ∨∨ ∃∃m. p1 = p2◖𝗦●m & (m●b)●q1 = q2
       | ∃∃m. q1 = m◖𝗦●q2 & (p1●b)●m = p2
.
