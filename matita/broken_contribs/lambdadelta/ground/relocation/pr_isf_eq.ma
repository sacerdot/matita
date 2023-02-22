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

include "ground/relocation/pr_fcla_eq.ma".
include "ground/relocation/pr_isf.ma".

(* FINITE COLENGTH CONDITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_eq *************************************************)

(*** isfin_eq_repl_back *)
lemma pr_isf_eq_repl_back:
      pr_eq_repl_back … pr_isf.
#f1 * /3 width=4 by pr_fcla_eq_repl_back, ex_intro/
qed-.

(*** isfin_eq_repl_fwd *)
lemma pr_isf_eq_repl_fwd: pr_eq_repl_fwd … pr_isf.
/3 width=3 by pr_isf_eq_repl_back, pr_eq_repl_sym/ qed-.
