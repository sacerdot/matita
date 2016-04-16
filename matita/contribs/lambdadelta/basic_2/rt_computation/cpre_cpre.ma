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

include "basic_2/computation/cprs_cprs.ma".
include "basic_2/computation/cpre.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS *************)

(* Main properties *********************************************************)

(* Basic_1: was: nf2_pr3_confluence *)
theorem cpre_mono: ∀G,L,T,T1. ⦃G, L⦄ ⊢ T ➡* 𝐍⦃T1⦄ → ∀T2. ⦃G, L⦄ ⊢ T ➡* 𝐍⦃T2⦄ → T1 = T2.
#G #L #T #T1 * #H1T1 #H2T1 #T2 * #H1T2 #H2T2
elim (cprs_conf … H1T1 … H1T2) -T #T #HT1
>(cprs_inv_cnr1 … HT1 H2T1) -T1 #HT2
>(cprs_inv_cnr1 … HT2 H2T2) -T2 //
qed-.
