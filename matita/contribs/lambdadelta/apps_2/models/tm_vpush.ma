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

include "ground/lib/exteq.ma".
include "apps_2/models/model_vpush.ma".
include "apps_2/models/tm.ma".

(* TERM MODEL ***************************************************************)

(* Properties with push for model evaluation ********************************)

lemma tm_vpush_vlift_join_O (h) (v) (T): ⇡[0]⫯{TM h}[0←T]v ≐ ⇡[0←↑[1]T]v.
#h #v #T #i
elim (eq_or_gt i) #Hi destruct
[ >mf_vpush_eq >mf_vlift_rw >vpush_eq //
| >mf_vpush_gt // >mf_vlift_rw >vpush_gt //
]
qed.
