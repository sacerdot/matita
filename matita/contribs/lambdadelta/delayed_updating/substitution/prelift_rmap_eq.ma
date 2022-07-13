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
include "ground/relocation/tr_pn_eq.ma".
include "ground/lib/stream_tls_eq.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

(* constructions with tr_map_eq *********************************************)

lemma prelift_rmap_eq_repl (l):
      stream_eq_repl … (λf1,f2. ↑[l]f1 ≗ ↑[l]f2).
* //
qed.
