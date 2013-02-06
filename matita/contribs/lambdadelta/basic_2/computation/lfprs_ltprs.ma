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

include "basic_2/computation/ltprs.ma".
include "basic_2/computation/lfprs.ma".

(* FOCALIZED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *********************)

(* Properties on context-free parallel computation for local environments ***)

lemma ltprs_lfprs: ∀L1,L2. L1 ➡* L2 → ⦃L1⦄ ➡* ⦃L2⦄.
/3 width=3/ qed.
