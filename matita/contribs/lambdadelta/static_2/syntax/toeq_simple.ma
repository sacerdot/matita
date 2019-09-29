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

include "static_2/syntax/term_simple.ma".
include "static_2/syntax/toeq.ma".

(* SORT-IRRELEVANT OUTER EQUIVALENCE FOR TERMS ******************************)

(* Properies with simple (neutral) terms ************************************)

(* Basic_2A1: was: simple_tsts_repl_dx *)
lemma simple_toeq_repl_dx: ∀T1,T2. T1 ⩳ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#T1 #T2 * -T1 -T2 //
#I #V1 #V2 #T1 #T2 #H
elim (simple_inv_pair … H) -H #J #H destruct //
qed-.

(* Basic_2A1: was: simple_tsts_repl_sn *)
lemma simple_toeq_repl_sn: ∀T1,T2. T1 ⩳ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
/3 width=3 by simple_toeq_repl_dx, toeq_sym/ qed-.
