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

include "ground/relocation/trz_puni.ma".
include "ground/relocation/trz_after.ma".
include "ground/notation/functions/uparrowplus_1.ma".

(* POSITIVE NEXT FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

interpretation
  "positive next (total relocation maps with integer)"
  'UpArrowPlus f = (trz_after trz_puni f).

(* Basic constructions ******************************************************)

lemma trz_pnext_eq_repl_fwd:
      compatible_2_fwd … trz_eq trz_eq (λf.↑⁺f).
/2 width=1 by trz_after_eq_repl/
qed.

lemma trz_after_pnext_sn (f2) (f1):
      ↑⁺(f2•f1) ≐ (↑⁺f2)•f1.
// qed.
