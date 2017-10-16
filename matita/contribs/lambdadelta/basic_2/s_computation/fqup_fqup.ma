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

include "basic_2/s_computation/fqup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

(* Main properties **********************************************************)

theorem fqup_trans: ∀b. tri_transitive … (fqup b).
/2 width=5 by tri_TC_transitive/ qed-.
