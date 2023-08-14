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
include "ground/relocation/fb/fbr_ctls_eq.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

(* constructions with map_eq ************************************************)

lemma prelift_rmap_eq_repl (l):
      compatible_2_fwd … fbr_eq fbr_eq (λf.🠢[l]f).
* /2 width=1 by fbr_ctl_eq_repl, fbr_eq_rcons_bi/
qed.

lemma prelift_rmap_id (l):
      (𝐢) ≐ 🠢[l]𝐢.
* [ #k || #F ] //
qed.
