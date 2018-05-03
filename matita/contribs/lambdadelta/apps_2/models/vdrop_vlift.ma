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

include "apps_2/models/model_vlift.ma".
include "apps_2/models/vdrop.ma".

(* EVALUATION DROP **********************************************************)

(* Advanced properties with evaluation evaluation lift **********************)

lemma vlift_vdrop_eq (M): ∀lv,i. lv ≐{?,dd M} ⫯[i←lv i]⫰[i]lv.
#M #lv #i #j elim (lt_or_eq_or_gt j i) #Hji destruct
[ >vlift_lt // >vdrop_lt //
| >vlift_eq //
| >vlift_gt // >vdrop_ge /2 width=1 by monotonic_pred/
  <(lt_succ_pred … Hji) //
]
qed.
