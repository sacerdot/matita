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

include "delayed_updating/substitution/lift_eq.ma".
include "ground/relocation/tr_compose_pap.ma".
include "ground/relocation/tr_compose_pn.ma".
include "ground/relocation/tr_compose_tls.ma".

(* LIFT FOR PATH ***********************************************************)

(* Constructions with tr_after *********************************************)

lemma lift_path_after (p) (f1) (f2):
      ↑[f2]↑[f1]p = ↑[f2∘f1]p.
#p elim p -p [| * ] // [ #n ] #p #IH #f1 #f2
[ <lift_path_d_sn <lift_path_d_sn <lift_path_d_sn //
| <lift_path_L_sn <lift_path_L_sn <lift_path_L_sn
  >tr_compose_push_bi //
]
qed.
