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

include "delayed_updating/substitution/prelift_rmap.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

(* constructions with trz_eq ************************************************)

lemma prelift_rmap_eq_repl (l):
      compatible_2_fwd … trz_eq trz_eq (λf.🠢[f]l).
* /2 width=1 by trz_tls_eq_repl, trz_push_eq_repl/
qed.
