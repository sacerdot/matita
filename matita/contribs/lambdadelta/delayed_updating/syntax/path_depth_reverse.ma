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

include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_reverse.ma".

(* DEPTH FOR PATH ***********************************************************)

(* Constructions with reverse ***********************************************)

lemma depth_reverse (p):
      ♭p = ♭pᴿ.
#p elim p -p //
* [ #n ] #p #IH <reverse_lcons
[ <depth_d_sn <depth_d_dx //
| <depth_m_sn <depth_m_dx //
| <depth_L_sn <depth_L_dx //
| <depth_A_sn <depth_A_dx //
| <depth_S_sn <depth_S_dx //
]
qed.
