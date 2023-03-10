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

include "static_2/relocation/lex_lex.ma".
include "basic_2/rt_computation/lpxs_lpx.ma".

(* EXTENDED PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS *************)

(* Main properties **********************************************************)

theorem lpxs_trans (G): Transitive … (lpxs G).
/4 width=5 by lpxs_cpxs_trans, cpxs_trans, lex_trans/ qed-.
