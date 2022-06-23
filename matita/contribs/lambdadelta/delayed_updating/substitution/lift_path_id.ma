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

include "delayed_updating/substitution/lift_gen_eq.ma".
include "ground/relocation/tr_id_pap.ma".
include "ground/relocation/tr_id_tls.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with proj_path and tr_id ***********************************)

lemma lift_path_id (p):
      p = ↑[𝐢]p.
#p elim p -p //
* [ #n ] #p #IH //
[ <lift_path_d_sn //
| <lift_path_L_sn //
]
qed.
