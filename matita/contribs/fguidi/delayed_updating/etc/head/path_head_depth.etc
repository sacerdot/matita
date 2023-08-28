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

include "delayed_updating/syntax/path_head.ma".
include "delayed_updating/syntax/path_height_labels.ma".
include "delayed_updating/syntax/path_depth_labels.ma".

(* HEAD FOR PATH ************************************************************)

(* Constructions with depth and height **************************************)

lemma path_head_depth (p) (n):
      n + ♯(↳[n]p) = ♭↳[n]p.
#p elim p -p // #l #p #IH
#n @(nat_ind_succ … n) -n // #n #_
cases l [ #k ]
[ <path_head_d_dx <height_d_dx <depth_d_dx <IH //
| <path_head_m_dx <height_m_dx <depth_m_dx //
| <path_head_L_dx <height_L_dx <depth_L_dx
  <nplus_succ_sn //
| <path_head_A_dx <height_A_dx <depth_A_dx //
| <path_head_S_dx <height_S_dx <depth_S_dx //
]
qed-. (**) (* gets in the way with auto *)
