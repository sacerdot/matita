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

include "delayed_updating/substitution/prelift_label.ma".
include "ground/relocation/fb/fbr_xapp_eq.ma".

(* PRELIFT FOR LABEL ********************************************************)

(* constructions with path_eq ***********************************************)

lemma prelift_label_eq_repl (l):
      compatible_2_fwd … fbr_eq (eq …) (λf.🠡[f]l).
* [ #k ] // #f1 #f2 #Hf
<prelift_label_d <prelift_label_d
<(fbr_xapp_eq_repl … Hf) -f2 //
qed.
