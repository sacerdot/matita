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

include "ground/relocation/tz/tzr_puni.ma".
include "ground/relocation/tz/tzr_after.ma".
include "ground/notation/functions/uparrowplus_1.ma".

(* POSITIVE NEXT FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

interpretation
  "positive next (total relocation maps with integer)"
  'UpArrowPlus f = (tzr_after tzr_puni f).

(* Basic constructions ******************************************************)

lemma tzr_pnext_eq_repl:
      compatible_2_fwd … tzr_eq tzr_eq (λf.↑⁺f).
/2 width=1 by tzr_after_eq_repl/
qed.

lemma tzr_after_pnext_sn (f2) (f1):
      ↑⁺(f2•f1) ≐ (↑⁺f2)•f1.
// qed.
