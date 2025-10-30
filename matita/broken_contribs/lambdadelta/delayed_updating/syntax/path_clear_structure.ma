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
include "delayed_updating/syntax/path_clear.ma".

(* CLEAR FOR PATH ***********************************************************)

(* Constructions with structure *********************************************)

lemma path_clear_structure (p):
      ⊗p = ⓪⊗p.
#p elim p -p //
* [ #k ] #p #IH //
qed.

lemma path_structure_clear (p):
      ⊗p = ⊗⓪p.
#p elim p -p //
* [ #k ] #p #IH //
<path_clear_d_dx //
qed.

lemma path_structure_clear_swap (p):
      ⓪⊗p = ⊗⓪p.
// qed-.

(* Inversions with structure ************************************************)

lemma eq_inv_path_clear_structure (p1) (p2):
      (⓪p1) = ⊗p2 → p1 = ⊗p2.
#p1 elim p1 -p1 //
* [ #k1 ] #p1 #IH #p2
[ <path_clear_d_dx #H0
  elim (eq_inv_d_dx_structure … H0)
| <path_clear_L_dx #H0
  elim (eq_inv_L_dx_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  <structure_append <structure_L_sx <(IH … Hr1) <Hr2 -IH -r1 -r2 //
| <path_clear_A_dx #H0
  elim (eq_inv_A_dx_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  <structure_append <structure_A_sx <(IH … Hr1) <Hr2 -IH -r1 -r2 //
| <path_clear_S_dx #H0
  elim (eq_inv_S_dx_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  <structure_append <structure_S_sx <(IH … Hr1) <Hr2 -IH -r1 -r2 //
]
qed-.
