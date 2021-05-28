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

include "ground/relocation/gr_fcla_eq.ma".
include "ground/relocation/gr_isf.ma".

(* FINITE COLENGTH CONDITION FOR GENERIC RELOCATION MAPS *)

(* Properties with gr_eq *)

(*** isfin_eq_repl_back *)
lemma gr_isf_eq_repl_back:
      gr_eq_repl_back … gr_isf.
#f1 * /3 width=4 by gr_fcla_eq_repl_back, ex_intro/
qed-.

(*** isfin_eq_repl_fwd *)
lemma gr_isf_eq_repl_fwd: gr_eq_repl_fwd … gr_isf.
/3 width=3 by gr_isf_eq_repl_back, gr_eq_repl_sym/ qed-.
