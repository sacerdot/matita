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

include "basic_2/reducibility/lfpr_cpr.ma".
include "basic_2/computation/cprs.ma".
include "basic_2/computation/lfprs.ma".

(* FOCALIZED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *********************)

(* Advanced properties ******************************************************)

lemma lfprs_pair_dx: ∀I,L1,L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀V1,V2. L2 ⊢ V1 ➡* V2 →
                     ⦃L1. ⓑ{I} V1⦄ ➡* ⦃L2. ⓑ{I} V2⦄.
#I #L1 #L2 #HL12 #V1 #V2 #H @(cprs_ind … H) -V2
/3 width=1/ /3 width=5/
qed.
(*
lamma lfprs_cprs_conf: ∀L1,L,L2,T1,T2. ⦃L1⦄ ➡* ⦃L2⦄ → L1 ⊢ T1 ➡* T2 → ⦃L1, T1⦄ ➡* ⦃L2, T2⦄.
*)
