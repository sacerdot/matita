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

include "delayed_updating/syntax/path_tail.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_height.ma".
(*
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_pred_succ.ma".
*)
(* TAIL FOR PATH ************************************************************)

(* Constructions with depth and height **************************************)

axiom depth_lablels_L (n):
      n = ♭(𝗟∗∗n).

axiom height_lablels_L (n):
      (𝟎) = ♯(𝗟∗∗n).

lemma tail_depth (p) (n):
      n + ♯(↳[n]p) = ♭↳[n]p.
#p elim p -p // #l #p #IH
#n @(nat_ind_succ … n) -n // #n #_
cases l [ #m ]
[ <tail_d_sn <height_d_sn <depth_d_sn //
| <tail_m_sn <height_m_sn <depth_m_sn //
| <tail_L_sn <height_L_sn <depth_L_sn
  <nplus_succ_sn //
| <tail_A_sn <height_A_sn <depth_A_sn //
| <tail_S_sn <height_S_sn <depth_S_sn //
]
qed.
