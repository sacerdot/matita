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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/substitution/lift_rmap_eq.ma".
include "delayed_updating/substitution/prelift_label_eq.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with map_eq ************************************************)

lemma lift_path_eq_repl (p):
      compatible_2_fwd … fbr_eq (eq …) (λf.🠡[f]p).
#p elim p -p //
#l #p #IH #f1 #f2 #Hf
<lift_path_rcons <lift_path_rcons
<(IH … Hf) -IH
/4 width=1 by prelift_label_eq_repl, lift_rmap_eq_repl, eq_f2/
qed.

(* Advanced constructions ***************************************************)

lemma lift_path_id (p):
      p = 🠡[𝐢]p.
#p elim p -p
/3 width=3 by prelift_label_eq_repl, eq_f2/
qed.
