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

include "explicit_updating/syntax/term_nexts.ma".
include "explicit_updating/notation/functions/xi_1.ma".

(* VARIABLE REFERENCE BY DEPTH FOR TERM *************************************)

(* Note: "↑*[↓p]𝛏" denoted "𝛏p" (source: λσ) *)
definition term_lref (p): 𝕋 ≝
           ↑*[↓p]𝛏.

interpretation
  "variable reference by depth (term)"
  'Xi p = (term_lref p).

(* Basic constructions ******************************************************)

lemma term_lref_unfold (p):
      ↑*[↓p]𝛏 = 𝛏❨p❩.
// qed.


lemma term_lref_unit:
      (𝛏) = 𝛏❨𝟏❩.
// qed.

lemma term_lref_succ (p):
      ↑𝛏❨p❩ = 𝛏❨↑p❩.
#p <term_lref_unfold <term_lref_unfold //
qed.
