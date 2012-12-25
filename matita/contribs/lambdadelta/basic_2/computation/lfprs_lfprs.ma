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

include "basic_2/reducibility/lfpr_lfpr.ma".
include "basic_2/computation/lfprs_cprs.ma".

(* FOCALIZED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *********************)

(* Advanced properties ******************************************************)

lemma lfprs_strip: ∀L,L1. ⦃L⦄ ➡* ⦃L1⦄ → ∀L2. ⦃L⦄ ➡ ⦃L2⦄ →
                   ∃∃L0. ⦃L1⦄ ➡ ⦃L0⦄ & ⦃L2⦄ ➡* ⦃L0⦄.
/3 width=3/ qed.

(* Main properties **********************************************************)

theorem lfprs_conf: ∀L,L1. ⦃L⦄ ➡* ⦃L1⦄ → ∀L2. ⦃L⦄ ➡* ⦃L2⦄ →
                    ∃∃L0. ⦃L1⦄ ➡* ⦃L0⦄ & ⦃L2⦄ ➡* ⦃L0⦄.
/3 width=3/ qed.

theorem lfprs_trans: ∀L1,L. ⦃L1⦄ ➡* ⦃L⦄ → ∀L2. ⦃L⦄ ➡* ⦃L2⦄ → ⦃L1⦄ ➡* ⦃L2⦄.
/2 width=3/ qed.

lemma lfprs_pair: ∀L1,L2. ⦃L1⦄ ➡* ⦃L2⦄ → ∀V1,V2. L2 ⊢ V1 ➡* V2 →
                  ∀I. ⦃L1. ⓑ{I} V1⦄ ➡* ⦃L2. ⓑ{I} V2⦄.
#L1 #L2 #H @(lfprs_ind … H) -L2 /2 width=1/
#L #L2 #_ #HL2 #IHL1 #V1 #V2 #HV12 #I
@(lfprs_trans … (L.ⓑ{I}V1)) /2 width=1/
qed.
