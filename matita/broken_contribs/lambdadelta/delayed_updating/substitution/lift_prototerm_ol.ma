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

include "ground/lib/subset_ol.ma".
include "delayed_updating/substitution/lift_prototerm.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with subset_ol *********************************************)

lemma term_ol_lift_bi (f) (t) (u):
      t ≬ u → 🠡[f]t ≬ 🠡[f]u.
#f #t #u * #r #H1r #H2r
/3 width=3 by in_comp_lift_bi, subset_ol_i/
qed.

(* Inversions with subset_ol ************************************************)

lemma term_ol_inv_lift_bi (f) (t) (u):
      (🠡[f]t) ≬ 🠡[f]u → t ≬ u.
#f #t #u * #r * #s1 #Hs1 #H1 * #s2 #Hs2 #H2 destruct
lapply (lift_path_inj … H2) -f #H0 destruct
/2 width=3 by subset_ol_i/
qed-.
