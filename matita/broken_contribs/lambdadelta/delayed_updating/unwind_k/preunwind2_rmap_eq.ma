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

include "delayed_updating/unwind_k/preunwind2_rmap.ma".
include "ground/relocation/fb/fbr_after_eq.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

(* Constructions with map_eq ************************************************)

lemma preunwind2_rmap_eq_repl (l):
      compatible_2_fwd … fbr_eq fbr_eq (λf.▶[l]f).
* // [ #k ] #f1 #f2 #Hf
/2 width=1 by fbr_after_eq_repl_bi, fbr_eq_rcons_bi/
qed.
