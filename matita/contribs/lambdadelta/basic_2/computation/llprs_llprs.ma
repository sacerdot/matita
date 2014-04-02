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

include "basic_2/computation/llprs.ma".

(* LAZY SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ***********************)

(* Main properties **********************************************************)

theorem llprs_trans: ∀G,T,d. Transitive … (llprs G d T).
normalize /2 width=3 by trans_TC/ qed-.
