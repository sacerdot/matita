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

include "basic_2/rt_computation/cprs_ctc.ma".
include "basic_2/rt_computation/lprs.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Properties with contextual transitive closure ****************************)

lemma lprs_CTC (h) (G):
               ∀L1,L2. L1⪤[CTC … (λL. cpm h G L 0)] L2 → ⦃G,L1⦄⊢ ➡*[h] L2.
/3 width=3 by cprs_CTC, lex_co/ qed.

(* Inversion lemmas with contextual transitive closure **********************)

lemma lprs_inv_CTC (h) (G):
                   ∀L1,L2. ⦃G,L1⦄⊢ ➡*[h] L2 → L1⪤[CTC … (λL. cpm h G L 0)] L2.
/3 width=3 by cprs_inv_CTC, lex_co/ qed-.
