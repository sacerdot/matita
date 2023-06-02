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

(* Constructions with trz_eq ************************************************)

lemma unwind2_path_eq_repl (p):
      compatible_2_fwd … trz_eq (eq …) (λf.▼[f]p).
* // * [ #k ] #p #f1 #f2 #Hf //
<unwind2_path_d_dx <unwind2_path_d_dx
lapply (unwind2_rmap_eq_repl … Hf) -Hf
[| #Hf <(trz_dapp_eq_repl_fwd … Hf) -f2 ] //
qed-.
