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

include "delayed_updating/unwind_k/unwind2_path_eq.ma".
include "delayed_updating/unwind_k/unwind2_rmap_after.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Properties with tr_after *************************************************)

lemma unwind2_path_after (g) (f) (p):
      ▼[g]▼[f]p = ▼[g∘f]p.
#g #f * // * [ #k ] #p //
<unwind2_path_d_dx <unwind2_path_d_dx
@eq_f2 // @eq_f >tr_compose_pap
/2 width=3 by tr_pap_eq_repl/
qed.
