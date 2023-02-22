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

include "delayed_updating/unwind_k/unwind2_path.ma".
include "delayed_updating/unwind_k/unwind2_rmap_eq.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Constructions with tr_map_eq *********************************************)

lemma unwind2_path_eq_repl (p):
      stream_eq_repl … (λf1,f2. ▼[f1]p = ▼[f2]p).
* // * [ #k ] #p #f1 #f2 #Hf //
<unwind2_path_d_dx <unwind2_path_d_dx
lapply (unwind2_rmap_eq_repl … Hf) -Hf
[| #Hf <(tr_pap_eq_repl … Hf) -f2 ] //
qed-.

