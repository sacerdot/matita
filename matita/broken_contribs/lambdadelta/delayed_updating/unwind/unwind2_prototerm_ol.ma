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

include "delayed_updating/unwind/unwind2_prototerm.ma".
include "ground/subsets/subset_ol.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with subset_ol *********************************************)

lemma term_ol_unwind2_bi (f) (t) (u):
      t ≬ u → ▼[f]t ≬ ▼[f]u.
#f #t #u * #r #H1r #H2r
/3 width=3 by in_comp_unwind2_bi, subset_ol_i/
qed.
