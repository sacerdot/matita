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

lemma path_head_structure_height (p) (n):
      ⊗↳[n]p = ↳[n+♯↳[n]p]⊗p.
#p elim p -p //
#l #p #IH #n @(nat_ind_succ … n) -n //
#n #_ cases l [ #k ]
[ <height_d_dx <structure_d_dx //
| <structure_m_dx //
| <structure_L_dx //
| <height_A_dx <structure_A_dx <nplus_succ_sn <path_head_A_dx //
| <height_S_dx <structure_S_dx <nplus_succ_sn <path_head_S_dx //
]
qed.

lemma path_head_structure_depth (p) (n):
      ⊗↳[n]p = ↳[♭↳[n]p]⊗p.
#p #n
<path_head_depth //
qed.
