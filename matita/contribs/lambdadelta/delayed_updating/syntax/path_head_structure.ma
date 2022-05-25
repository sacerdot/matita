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

include "delayed_updating/syntax/path_head_depth.ma".
include "delayed_updating/syntax/path_structure_labels.ma".

(* HEAD FOR PATH ************************************************************)

(* Constructions with structure *********************************************)

lemma path_head_structure_height (p) (m):
      ⊗↳[m]p = ↳[m+♯↳[m]p]⊗p.
#p elim p -p //
#l #p #IH #m @(nat_ind_succ … m) -m //
#m #_ cases l [ #n ]
[ <height_d_sn <structure_d_sn //
| <structure_m_sn //
| <structure_L_sn //
| <height_A_sn <structure_A_sn <nplus_succ_sn <path_head_A_sn //
| <height_S_sn <structure_S_sn <nplus_succ_sn <path_head_S_sn //
]
qed.

lemma path_head_structure_depth (p) (m):
      ⊗↳[m]p = ↳[♭↳[m]p]⊗p.
#p #m
<path_head_depth //
qed.
