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

include "delayed_updating/unwind/preunwind2_rmap.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/relocation/tr_pn_eq.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

(* Constructions with tr_map_eq *********************************************)

lemma preunwind2_rmap_eq_repl (l):
      stream_eq_repl … (λf1,f2. ▶[f1]l ≗ ▶[f2]l).
* // #k #f1 #f2 #Hf
/2 width=1 by tr_compose_eq_repl/
qed-.
