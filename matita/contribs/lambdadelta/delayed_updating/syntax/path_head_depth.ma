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
include "delayed_updating/syntax/path_depth_labels.ma".
include "delayed_updating/syntax/path_height_labels.ma".

(* HEAD FOR PATH ************************************************************)

(* Constructions with depth and height **************************************)

lemma path_head_depth (p) (n):
      n + ♯(↳[n]p) = ♭↳[n]p.
#p elim p -p // #l #p #IH
#n @(nat_ind_succ … n) -n // #n #_
cases l [ #m ]
[ <path_head_d_sn <height_d_sn <depth_d_sn //
| <path_head_m_sn <height_m_sn <depth_m_sn //
| <path_head_L_sn <height_L_sn <depth_L_sn
  <nplus_succ_sn //
| <path_head_A_sn <height_A_sn <depth_A_sn //
| <path_head_S_sn <height_S_sn <depth_S_sn //
]
qed.
