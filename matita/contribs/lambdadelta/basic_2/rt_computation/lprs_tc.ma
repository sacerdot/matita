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

include "basic_2/relocation/lex_tc.ma".
include "basic_2/rt_computation/lprs_ctc.ma".
include "basic_2/rt_computation/cprs_lpr.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Properties with transitive closure ***************************************)

lemma lprs_TC (h) (G):
              ∀L1,L2. TC … (lex (λL.cpm h G L 0)) L1 L2 → ⦃G, L1⦄⊢ ➡*[h] L2.
/4 width=3 by lprs_CTC, lex_CTC, lpr_cprs_trans/ qed.

(* Inversion lemmas with transitive closure *********************************)

lemma lprs_inv_TC (h) (G):
                  ∀L1,L2. ⦃G, L1⦄⊢ ➡*[h] L2 → TC … (lex (λL.cpm h G L 0)) L1 L2.
/3 width=3 by lprs_inv_CTC, lex_inv_CTC/ qed-.
