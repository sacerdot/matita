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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/unwind/preunwind2_rmap_eq.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with map_eq ************************************************)

lemma unwind2_rmap_eq_repl (p:path):
      compatible_2_fwd … fbr_eq fbr_eq (λf.▶[p]f).
#p elim p -p //
#l #p #IH #f1 #f2 #Hf
/3 width=1 by preunwind2_rmap_eq_repl/
qed.
