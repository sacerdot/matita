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

(* Constructions with path_eq ***********************************************)

lemma lift_path_eq_repl (p):
      stream_eq_repl … (λf1,f2. ↑[f1]p = ↑[f2]p).
#p elim p -p //
#l #p #IH #f1 #f2 #Hf
<lift_path_rcons <lift_path_rcons
@eq_f2 (**) (* auto fails *)
[ /3 width=1 by lift_rmap_eq_repl, prelift_label_eq_repl/
| @IH -IH //
]
qed.
