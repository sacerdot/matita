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

include "apps_2/models/model_li.ma".
include "apps_2/models/veq.ma".

(* EVALUATION EQUIVALENCE  **************************************************)

(* Properties with local environment interpretation *************************)

lemma li_repl_back (M) (gv): is_model M →
                             ∀L,lv1. lv1 ϵ ⟦L⟧[gv] →
                             ∀lv2. lv1 ≗{M} lv2 → lv2 ϵ ⟦L⟧[gv].
#M #gv #HM #L #lv1 #H elim H -L -lv1 //
[ #lv1 #d1 #K #V #_ #Hd #IH #y #H
  elim (veq_inv_push_sn … H) -H #lv2 #d2 #Hlv12 #Hd12 #H destruct
  /4 width=5 by li_abbr, ti_comp_l, mr/
| #lv1 #d1 #K #W #_ #IH #y #H
  elim (veq_inv_push_sn … H) -H #lv2 #d2 #Hlv12 #_ #H destruct
  /3 width=1 by li_abst/
| #lv1 #d1 #I #K #_ #IH #y #H
  elim (veq_inv_push_sn … H) -H #lv2 #d2 #Hlv12 #_ #H destruct
  /3 width=1 by li_unit/
]
qed-.
