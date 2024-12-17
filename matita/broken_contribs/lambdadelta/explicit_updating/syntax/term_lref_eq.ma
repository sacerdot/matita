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

include "explicit_updating/syntax/term_nexts_eq.ma".
include "explicit_updating/syntax/term_lref.ma".

(* VARIABLE REFERENCE BY DEPTH FOR TERM *************************************)

(* Inversions with term_eq **************************************************)

lemma term_eq_inv_lref_bi (p1) (p2):
      (𝛏p1) ≐ (𝛏p2) → p1 = p2.
/3 width=2 by term_eq_inv_nexts_unit_bi, eq_inv_pnpred_bi/
qed-.
