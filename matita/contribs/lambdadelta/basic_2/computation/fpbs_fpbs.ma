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

include "basic_2/computation/fpbs.ma".

(* "QRST" PARALLEL COMPUTATION FOR CLOSURES *********************************)

(* Main properties **********************************************************)

theorem fpbs_trans: ∀h,o. tri_transitive … (fpbs h o).
/2 width=5 by tri_TC_transitive/ qed-.
