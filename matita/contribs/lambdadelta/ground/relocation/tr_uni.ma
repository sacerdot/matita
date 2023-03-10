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

include "ground/arith/nat_succ.ma".
include "ground/notation/functions/element_u_1.ma".
include "ground/relocation/tr_id.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS *******************************)

definition tr_uni (n:nat): tr_map ā ān āØ® š¢.

interpretation
  "uniform elements (total relocation maps)"
  'ElementU n = (tr_uni n).

(* Basic constructions ******************************************************)

lemma tr_uni_unfold (n): ān āØ® š¢ = š®āØnā©.
// qed.

lemma tr_uni_zero: š¢ = š®āØšā©.
<tr_id_unfold //
qed.

lemma tr_uni_succ (n): āš®āØnā© = š®āØānā©.
// qed.
