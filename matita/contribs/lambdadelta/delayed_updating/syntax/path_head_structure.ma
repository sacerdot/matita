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
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".

(* HEAD FOR PATH ************************************************************)

(* Constructions with structure *********************************************)

axiom path_head_structure (p) (q):
      ⊗p = ↳[♭⊗p]((⊗p)●q).
(*
#p elim p -p
[ #q <path_head_zero //
| * [ #n ] #p #IH #q
  [ <structure_d_sn //
  | <structure_m_sn //
  | <structure_L_sn
  | <structure_A_sn <list_append_lcons_sn 
    <path_head_A_sn //
  | <structure_S_sn //
  ]
]
*)