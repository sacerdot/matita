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
include "ground/relocation/tr_pap_eq.ma".

(* PRELIFT FOR LABEL ********************************************************)

(* constructions with tr_map_eq *********************************************)

lemma prelift_label_eq_repl (l):
      stream_eq_repl … (λf1,f2. ↑[f1]l = ↑[f2]l).
* //
#k #f1 #f2 #Hf
<prelift_label_d <prelift_label_d
/3 width=1 by tr_pap_eq_repl, eq_f/
qed.
